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
const parseBridge = (namePtr, nameLen, outPtr) => {
  if (!compilerMemory) {
    throw new Error("compiler memory not initialized before parse call");
  }

  const compilerName = new Uint8Array(compilerMemory.buffer, namePtr, nameLen);
  const pluginNamePtr = pluginExports.__wbindgen_malloc(nameLen, 1);
  new Uint8Array(pluginExports.memory.buffer).set(compilerName, pluginNamePtr);

  const pluginOutPtr = pluginExports.__wbindgen_malloc(8, 8);
  const status = pluginExports.parse(pluginNamePtr, nameLen, pluginOutPtr);
  if (status === 0) {
    const jetBytes = new Uint8Array(pluginExports.memory.buffer, pluginOutPtr, 8);
    new Uint8Array(compilerMemory.buffer).set(jetBytes, outPtr);
  }

  return status;
};

// 2) Instantiate compiler wasm and satisfy its plugin imports.
const compiler = await instantiateWasm(compilerPath, {
  ...wasmBindgenShimImports(),
  "simplicityhl-plugin": {
    ...pluginExports,
    parse: parseBridge,
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
