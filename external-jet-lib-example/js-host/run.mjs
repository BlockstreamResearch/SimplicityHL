import { readFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const repoRoot = path.resolve(__dirname, "..", "..");
// Default plugin wasm (the external jet library compiled as wasm).
const defaultPluginPath = path.join(
  repoRoot,
  "target",
  "wasm32-unknown-unknown",
  "debug",
  "external_jet_lib_example.wasm"
);
// Default compiler wasm (the host that imports jets from the plugin).
const defaultCompilerPath = path.join(
  repoRoot,
  "target",
  "wasm32-unknown-unknown",
  "debug",
  "compiler-wasm.wasm"
);

const pluginPath = process.argv[2] ?? defaultPluginPath;
const compilerPath = process.argv[3] ?? defaultCompilerPath;

async function instantiateWasm(filePath, imports = {}) {
  const bytes = await readFile(filePath);
  return WebAssembly.instantiate(bytes, imports);
}

// Minimal wasm-bindgen imports expected by these binaries.
function wasmBindgenShimImports() {
  return {
    __wbindgen_placeholder__: {
      __wbindgen_describe() {
        // No-op for this standalone host path.
      },
      __wbindgen_throw() {
        throw new Error("wasm-bindgen runtime requested a throw");
      },
    },
    __wbindgen_externref_xform__: {
      __wbindgen_externref_table_grow() {
        return -1;
      },
      __wbindgen_externref_table_set_null() {
        // No-op for this standalone host path.
      },
    },
  };
}

// 1) Load the plugin first so we can pass its exports as compiler imports.
const plugin = await instantiateWasm(pluginPath, wasmBindgenShimImports());
const pluginExports = plugin.instance.exports;
let compilerMemory = null;

function requireCompilerMemory() {
  if (!compilerMemory) {
    throw new Error("compiler memory not initialized before a plugin call");
  }
  return compilerMemory;
}

function byteBridge(pluginFn, retToByteLen = (ret) => ret) {
  return (jetIndex, outPtr, cap) => {
    const compiler = requireCompilerMemory();
    const capNum = Number(cap);
    const pluginPtr = pluginExports.__wbindgen_malloc(capNum, 1);
    try {
      const ret = pluginFn(jetIndex, pluginPtr, capNum);
      if (ret >= 0) {
        const nBytes = Math.min(retToByteLen(ret), capNum);
        if (nBytes > 0) {
          const src = new Uint8Array(pluginExports.memory.buffer, pluginPtr, nBytes);
          new Uint8Array(compiler.buffer).set(src, Number(outPtr));
        }
      }
      return ret;
    } finally {
      pluginExports.__wbindgen_free(pluginPtr, capNum, 1);
    }
  };
}

// `parse` moves bytes in both directions: a name from the compiler to the
// plugin, and the resulting 8-byte ExternalJet handle back again.
const parseBridge = (namePtr, nameLen, outPtr) => {
  const compiler = requireCompilerMemory();
  const compilerName = new Uint8Array(compiler.buffer, namePtr, nameLen);
  const pluginNamePtr = pluginExports.__wbindgen_malloc(nameLen, 1);
  new Uint8Array(pluginExports.memory.buffer).set(compilerName, pluginNamePtr);

  const pluginOutPtr = pluginExports.__wbindgen_malloc(8, 8);
  try {
    const status = pluginExports.parse(pluginNamePtr, nameLen, pluginOutPtr);
    if (status === 0) {
      const jetBytes = new Uint8Array(pluginExports.memory.buffer, pluginOutPtr, 8);
      new Uint8Array(compiler.buffer).set(jetBytes, outPtr);
    }
    return status;
  } finally {
    pluginExports.__wbindgen_free(pluginNamePtr, nameLen, 1);
    pluginExports.__wbindgen_free(pluginOutPtr, 8, 8);
  }
};

// 2) Instantiate compiler wasm and satisfy its plugin imports. Pointer-bearing
//    entry points are bridged; the scalar ones pass straight through.
const compiler = await instantiateWasm(compilerPath, {
  ...wasmBindgenShimImports(),
  "simplicityhl-plugin": {
    cmr: byteBridge(pluginExports.cmr),
    source_ty: byteBridge(pluginExports.source_ty),
    target_ty: byteBridge(pluginExports.target_ty),
    display: byteBridge(pluginExports.display),
    source_jet_classification: byteBridge(pluginExports.source_jet_classification),
    target_jet_classification: byteBridge(pluginExports.target_jet_classification),
    encode: byteBridge(pluginExports.encode, (bits) => (bits + 7) >> 3),
    parse: parseBridge,
    // Scalar-only ABI (integers / the pointer-free ExternalJet handle).
    cost: pluginExports.cost,
    is_disabled: pluginExports.is_disabled,
    verify: pluginExports.verify,
  },
});
compilerMemory = compiler.instance.exports.memory;

const getCompilerLastError = () => {
  const ptrFn = compiler.instance.exports.last_error_ptr;
  const lenFn = compiler.instance.exports.last_error_len;
  if (typeof ptrFn !== "function" || typeof lenFn !== "function") {
    return "";
  }

  const ptr = ptrFn();
  const len = lenFn();
  if (!ptr || !len) {
    return "";
  }

  const bytes = new Uint8Array(compilerMemory.buffer, ptr, len);
  return new TextDecoder().decode(bytes);
};

// 3) Execute the compiler entrypoint that compiles `assert!(true)` via plugin jets.
const compileFn = compiler.instance.exports.compile_happyjet;
if (typeof compileFn !== "function") {
  throw new Error("compiler wasm does not export compile_happyjet");
}

const rc = compileFn();
if (rc !== 0) {
  const err = getCompilerLastError();
  throw new Error(`compile_happyjet failed with status ${rc}${err ? `: ${err}` : ""}`);
}

console.log("HappyJet compilation succeeded via wasm plugin linkage.");

// 4) Exercise every bridged shim (cmr, types, encode, display, classifications)
//    and validate the bytes that cross the module-memory boundary.
const probeFn = compiler.instance.exports.probe_external_jet;
if (typeof probeFn !== "function") {
  throw new Error("compiler wasm does not export probe_external_jet");
}

const probeRc = probeFn();
if (probeRc !== 0) {
  const err = getCompilerLastError();
  throw new Error(
    `probe_external_jet failed with status ${probeRc}${err ? `: ${err}` : ""}`
  );
}

console.log("External jet ABI probe passed: all shims round-trip across separate module memories.");
