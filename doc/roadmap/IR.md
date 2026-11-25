# IR-3: Object file format

Owner: stringhandler

Status: Proposed. 

## Motivation

Wallets should not compile SimplicityHL. Compiler versions change, and a
wallet cannot be expected to carry several versions or to reproduce the same
Simplicity node tree and CMR from SimplicityHL source. The object file is the
compiled form of a contract that a wallet can use without a compiler.

Without a compiler, a wallet needs from the object:

- the parameter schema and body CMR, to derive the address of any instance it
  receives at or pays to;
- the unpruned, compiled body, to build the spending program;
- the parameters, to instantiate the contract in a particular configuration;
- the witnesses, to know what values a spend must supply;
- which witnesses are signatures, under which key and over which message.

The last item is not derivable from names and types. SimplicityHL's HTLC
example has one
witness, `COMPLETE_OR_CANCEL: Either<(u256, Signature), Signature>`, holding
two signatures under two keys. Nothing in the name or the type says so.

The object is produced by `simc` from `.simf` files. It is consumed by a
linker in rust-simplicity, which combines the object with parameter values and
witness values to produce a finalised program. The object format is specified
here. There is a JSON form and a binary form. Descriptors and the transaction
manifest are specified in later documents. The PSET fields are summarised
below and specified in an ELIP.

## Object

An escrow settled by an oracle. The recipient can settle with an oracle's
attestation of the outcome, and the sender can refund after a timeout. A
selector witness chooses the path, each wallet signature is its own bare
witness, and the keys are parameters. The attributes above `main` are new
syntax, discussed under Compiler changes.

```rust
#[sig(RECIPIENT_SIG, key = param::RECIPIENT_KEY)]
#[sig(SENDER_SIG, key = param::SENDER_KEY)]
fn main() {
    match witness::SETTLE {
        true => {
            let outcome: u256 = witness::OUTCOME;
            let oracle_sig: Signature = witness::ORACLE_SIG;
            jet::bip_0340_verify((param::ORACLE_KEY, outcome), oracle_sig);
            let sig: Signature = witness::RECIPIENT_SIG;
            settle(outcome, param::RECIPIENT_KEY, sig);
        },
        false => {
            jet::check_lock_height(param::REFUND_HEIGHT);
            let sig: Signature = witness::SENDER_SIG;
            refund(param::SENDER_KEY, sig);
        },
    }
}
```

Its object, in the JSON form:

```json
{
  "sof_json": 0,
  "jet_set": { "name": "elements", "hash": "<hash>" },
  "body": "<base64>",
  "body_cmr": "<hex>",
  "source_language": "simplicityhl",
  "params": [
    { "name": "RECIPIENT_KEY", "type": "2^256", "source_type": "Pubkey" },
    { "name": "SENDER_KEY",    "type": "2^256", "source_type": "Pubkey" },
    { "name": "ORACLE_KEY",    "type": "2^256", "source_type": "Pubkey" },
    { "name": "REFUND_HEIGHT", "type": "2^32",  "source_type": "Height" }
  ],
  "witnesses": [
    { "name": "SETTLE",        "type": "2",     "source_type": "bool" },
    { "name": "OUTCOME",       "type": "2^256", "source_type": "u256" },
    { "name": "ORACLE_SIG",    "type": "2^512", "source_type": "Signature" },
    { "name": "RECIPIENT_SIG", "type": "2^512", "source_type": "Signature" },
    { "name": "SENDER_SIG",    "type": "2^512", "source_type": "Signature" }
  ],
  "signatures": {
    "RECIPIENT_SIG": { "scheme": "bip340", "key": { "param": "RECIPIENT_KEY" }, "message_builder": { "jet": "sig_all_hash" } },
    "SENDER_SIG":    { "scheme": "bip340", "key": { "param": "SENDER_KEY" },    "message_builder": { "jet": "sig_all_hash" } }
  },
  "provenance": { ... }
}
```

To settle, `SETTLE` is `true`, `OUTCOME` and `ORACLE_SIG` are supplied from
the oracle, and the recipient signs. `SENDER_SIG` is pruned. To refund,
`SETTLE` is `false` and the sender signs. `OUTCOME`, `ORACLE_SIG` and
`RECIPIENT_SIG` are pruned.

`ORACLE_SIG` has the same type as the two wallet signatures but is not listed
under `signatures`. It is a signature over the outcome, not over the
transaction, and the oracle is not a party to the spend.

`sof_json` is the version of the JSON form. A change that alters how a linker
reads an object bumps it; adding an optional field does not.

`body` is the Simplicity bit encoding of the unpruned body without witness
data, in base64. `body_cmr` is its CMR.

Parameter and witness names are written as the source spells them. Each
parameter and witness carries its Simplicity type in canonical text form and,
optionally, the type as the source language writes it. `source_type` is for
tools that understand the source language, such as a transaction manifest.
Linkers ignore it.

The order of `params` is significant. The linker assembles the parameter
values into the body's input in this order, and nothing else records it.

Each witness is one entry, filled whole at spend time. There are no paths into
a witness and no names for its parts. Witness names are unique within a
program, and match the source when provenance is given. The order of
`witnesses` does not matter for linking. It should match the order the
witnesses appear in the encoded body, but is not required to.

`signatures` lists the witnesses a PSBT or PSET signer fills, and `jet_set`
identifies the jet set the body uses. Both are described below.

`provenance` is optional. It records the compiler and its exact version, the
options that affect output, the entry point, the SHA-256 of each source file,
and optionally a repository URL and commit. A third party, such as a metadata
registry, fetches the sources, checks them against the hashes, rebuilds the
object and compares the body CMR and schemas. Linkers ignore it.

The JSON form is described by [sof-object.schema.json](sof-object.schema.json).
The binary form carries the same fields with CompactSize lengths and is what a
descriptor embeds; it is not specified here.

## Signatures

Hardware signers and other PSBT signers communicate only through PSBT and PSET
fields. They cannot read a transaction manifest or construct a Simplicity
value. Every other witness is assumed to be filled by more capable software
that can parse and insert Simplicity values. Signatures are therefore the one
kind of witness the object describes beyond name and type.

The object contains a `signatures` map keyed by witness name:

```json
"signatures": {
  "RECIPIENT_SIG": {
    "scheme": "bip340",
    "key": { "param": "RECIPIENT_KEY" },
    "message_builder": { "jet": "sig_all_hash" }
  }
}
```

A witness listed here has type `Signature`. The linker fills it from a
signature produced by the named key. A signature nested in any other type,
including `Option<Signature>`, cannot be listed: a PSBT signer produces a
signature or nothing, and cannot express an absent one. Which path a spend
takes is chosen by software, through an ordinary witness, not by who signed.

`key` names a parameter. The PSET Updater uses it to copy the key's origin from
the descriptor's BIP 380 key expression into the PSET, where the signer finds
it. `key` is omitted when the program takes the key from a constant or a
witness; the Updater then supplies the key from the manifest. Derivation paths
never appear in the object.

`scheme` is `bip340`. No other value is defined.

`message_builder` says how the signed message is computed. It is an object
with one tag. The only tag defined is `jet`, whose value is the name of a jet
of type `1 → 2^256`, and the only jet defined is `sig_all_hash`. A signer that
does not recognise the tag or the jet must not sign. Later versions may define
a tag carrying an arbitrary Simplicity expression (see SYN-7).

A `Signature`-typed witness that is not listed in `signatures` is an ordinary
value. `ORACLE_SIG` in the example is one; signatures over other sighash modes
are another.

Because witness names are unique, a key used in two branches has two
witnesses. The Updater requests a signature only for the one on the path
taken, and pruning drops the other.

## Jet set

`jet_set` is an object:

```json
"jet_set": { "name": "elements", "hash": "<hash>" }
```

`name` is for display only. Both `bitcoin` and `elements` are defined.

`hash` identifies the jet set by its canonical jet table. The table has one row
per jet, in the order of the jets' bit encodings. Each row is:

| Field | Encoding |
|---|---|
| encoding | the jet's bit-encoding code, as a CompactSize length in bits followed by the bits, zero-padded to a byte boundary |
| cmr | 32 bytes |
| source type | canonical text form, as a CompactSize length followed by the bytes |
| target type | canonical text form, as above |
| cost | milli weight units, as a CompactSize |

The hash is `SHA256(SHA256("Simplicity\x1fJetSet") ‖ rows)`, with the rows
concatenated in order. Costs are included because the budget and the padding
depend on them. The table is defined by the jet set's reference implementation
in rust-simplicity, and two implementations that disagree on any field produce
different hashes.

## Linking

An object is a body `f : P → 1`. Linking binds parameter values to produce a
complete `1 → 1` program under a named strategy. The descriptor records the
strategy so that another can be added later without changing existing
addresses. The only strategy defined is `const`:

```
main := comp (scribe p) f
```

where `scribe p` is a right-nested pair of one constant per parameter, in
`params` order.

Parameter values come from the descriptor or the transaction manifest, and a
wallet may take some from its user interface. They must be known before the
PSET is created, since the address depends on them.

A redeem program may not contain two nodes with the same identity hash. Where
a constant in `scribe p` coincides with a constant in `f`, the linker merges
them, so the linked program's shape depends on the parameter values.

To spend, the linker:

1. builds the program under the instance's strategy and checks that the
   witness schema matches it;
2. fills each non-signature witness from its value;
3. fills each signature witness from the signature supplied for its key;
4. prunes the program for this transaction. A witness with no value whose node
   survives pruning is an error.

The input's witness stack is the witness data, the program, the CMR and the
control block.

## Compiler changes

`simc` must:

- accept an attribute marking a witness as a signature slot, naming the key
  parameter and defaulting to `bip340` and `jet::sig_all_hash()`;
- emit `signatures` and the structured `jet_set`;
- reject an attribute that names an unknown witness, a witness whose type is
  not `Signature`, a duplicate attribute, or a `key` that is not a parameter.

The attribute syntax is a language feature in its own right and gets its own
roadmap entry. The example under Object shows a sketch of it.

`param::X` must resolve in every function, not only in `main`. If that proves
hard, parameters may be restricted to `main` at first. Witnesses remain
`main`-only, as upstream already requires, since a witness inside a function
inlined twice would become two witness nodes.

A program whose witness type nests a `Signature`, in an enum or any other
compound type, still compiles to an object. The compiler warns, since no PSBT
signer can fill such a witness:

```
warning: witness `COMPLETE_OR_CANCEL` nests a signature, which PSBT signers cannot fill
```

## PSET changes

The ELIP adds these per-input fields:

| Name | Key data | Value data |
|---|---|---|
| `PSBT_SIMPLICITY_IN_OBJECT` | `<32-byte cmr>` | The leaf's `sof(...)` descriptor, carrying the object and the parameter values |
| `PSBT_SIMPLICITY_IN_WITNESS` | `<32-byte cmr> <witness name>` | The whole value of a non-signature witness, in the compact encoding at its type |
| `PSBT_SIMPLICITY_IN_KEY` | `<32-byte cmr> <witness name>` | The key expected to sign a signature witness, with its origin, copied from the descriptor by the Updater |
| `PSBT_SIMPLICITY_IN_SIGNATURE` | `<32-byte cmr> <witness name>` | A BIP 340 signature for a signature witness, written by the Signer |

A matching per-output field carries the object for an output being paid to.

Settling the escrow above, after the Updater and before the Signer. `<cmr>` is
the leaf's CMR and `<xonly>` a 32-byte key:

```
IN_OBJECT     <cmr>                  sof(const,<object>,RECIPIENT_KEY=[d34db33f/86'/1776'/0'/0/5]<xonly>,SENDER_KEY=<xonly>,ORACLE_KEY=<xonly>,REFUND_HEIGHT=800000)
IN_WITNESS    <cmr> "SETTLE"         80
IN_WITNESS    <cmr> "OUTCOME"        <32 bytes>
IN_WITNESS    <cmr> "ORACLE_SIG"     <64 bytes>
IN_KEY        <cmr> "RECIPIENT_SIG"  <xonly> d34db33f 86' 1776' 0' 0 5
```

The Updater has followed `signatures.RECIPIENT_SIG.key.param` to the
`RECIPIENT_KEY` expression in the descriptor and written the derived key and
its origin as `IN_KEY`. It writes no `IN_KEY` for `SENDER_SIG`, since this
spend does not take that path. The recipient's signer matches the origin
against its seed, links the object to check the CMR, computes `sig_all_hash`
as `message_builder` says, and adds:

```
IN_SIGNATURE  <cmr> "RECIPIENT_SIG"  <64 bytes>
```

The Finalizer fills the four witnesses from these fields, prunes `SENDER_SIG`
with the refund path, and builds the witness stack. The field layout and the
roles' duties are specified in the ELIP.


