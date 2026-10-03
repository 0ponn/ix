module
public import Ix.Aiur.Semantics.BytecodeFfi

/-!
AiurSystem, Proof, FRI params, and `buildClaim` — the "prove & verify" FFI surface.

The bytecode-execution FFI that used to live here has moved to
`Ix/Aiur/Bytecode/ExecuteFfi.lean` so that `Bytecode/Eval.lean` can be built
without pulling in the proving backend.
-/

public section

namespace Aiur

private opaque PoofNonempty : NonemptyType
def Proof : Type := PoofNonempty.type
instance : Nonempty Proof := PoofNonempty.property

namespace Proof

@[extern "rs_aiur_proof_to_bytes"]
opaque toBytes : @& Proof → ByteArray

@[extern "rs_aiur_proof_of_bytes"]
opaque ofBytes : @& ByteArray → Proof

/-- Decode an untrusted serialized proof without aborting the process. Store
and network boundaries must use this variant; `ofBytes` remains for callers
whose bytes were produced in-process or already validated. -/
@[extern "rs_aiur_proof_of_bytes_checked"]
opaque ofBytesChecked : @& ByteArray → Except String Proof

/-- The per-circuit log2 trace heights this proof publishes. -/
@[extern "rs_aiur_proof_log_degrees"]
opaque logDegrees : @& Proof → Array Nat

end Proof

structure CommitmentParameters where
  logBlowup : Nat
  capHeight : Nat

structure FriParameters where
  logFinalPolyLen : Nat
  maxLogArity : Nat
  numQueries : Nat
  commitProofOfWorkBits : Nat
  queryProofOfWorkBits : Nat

private opaque AiurSystemNonempty : NonemptyType
def AiurSystem : Type := AiurSystemNonempty.type
instance : Nonempty AiurSystem := AiurSystemNonempty.property

namespace AiurSystem

@[extern "rs_aiur_system_build"]
opaque build : @&Bytecode.Toplevel → @&CommitmentParameters → @&FriParameters → AiurSystem

/-- Serialize the verifying key (`System<AiurCircuit>`) to bytes. -/
@[extern "rs_aiur_system_vk_bytes"]
opaque vkBytes : @& AiurSystem → ByteArray

@[extern "rs_aiur_system_prove"]
private opaque prove' : @& AiurSystem →
  @& Bytecode.FunIdx → @& Array G →
  (ioData : @& Array (G × Array G)) →
  (ioMap : @& Array ((G × Array G) × IOKeyInfo)) →
    Array G × Proof × Array (G × Array G) × Array ((G × Array G) × IOKeyInfo)

/-- Executes the bytecode function `funIdx` with the given `args` and `ioBuffer`,
then generates a proof of the computation. Returns the claim
(`#[functionChannel, funIdx] ++ args ++ output`), the `Proof`, and the
updated `IOBuffer`. -/
def prove (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Array G × Proof × IOBuffer :=
  let ioData := ioBuffer.data.toArray
  let ioMap := ioBuffer.map.toArray
  let (claim, proof, ioData, ioMap) := prove' system funIdx args
    ioData ioMap
  let ioData := ioData.foldl (fun acc (k, v) => acc.insert k v) ∅
  let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
  (claim, proof, ⟨ioData, ioMap⟩)

@[extern "rs_aiur_system_prove_padded"]
private opaque provePadded' : @& AiurSystem →
  @& Bytecode.FunIdx → @& Array G →
  (ioData : @& Array (G × Array G)) →
  (ioMap : @& Array ((G × Array G) × IOKeyInfo)) →
  (floors : @& Array Nat) →
    Array G × Proof × Array (G × Array G) × Array ((G × Array G) × IOKeyInfo)

/-- `prove`, padding circuit `i` to at least `floors[i]` rows (circuit order
of the system, as returned by `traceHeights`). Proving every witness at one
fixed set of floors makes the per-circuit heights in the proof, and so
`Proof.logDegrees`, independent of the witness. -/
def provePadded (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer)
  (floors : @& Array Nat) : Array G × Proof × IOBuffer :=
  let (claim, proof, ioData, ioMap) := provePadded' system funIdx args
    ioBuffer.data.toArray ioBuffer.map.toArray floors
  let ioData := ioData.foldl (fun acc (k, v) => acc.insert k v) ∅
  let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
  (claim, proof, ⟨ioData, ioMap⟩)

@[extern "rs_aiur_system_trace_heights"]
private opaque traceHeights' : @& AiurSystem →
  @& Bytecode.FunIdx → @& Array G →
  (ioData : @& Array (G × Array G)) →
  (ioMap : @& Array ((G × Array G) × IOKeyInfo)) → Array Nat

/-- Per-circuit trace heights an execution of `funIdx` produces, without
proving. -/
def traceHeights (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Array Nat :=
  traceHeights' system funIdx args ioBuffer.data.toArray ioBuffer.map.toArray

@[extern "rs_aiur_system_prove_ixvm"]
private opaque proveIxVM' : @& AiurSystem →
  @& Bytecode.FunIdx → @& Array G →
  (ioData : @& Array (G × Array G)) →
  (ioMap : @& Array ((G × Array G) × IOKeyInfo)) →
    Array G × Proof × Array (G × Array G) × Array ((G × Array G) × IOKeyInfo)

/-- IxVM-native prove: same shape as `prove`, but routes execution
    through the codegen'd Rust kernel (`execute_generated`) instead
    of the bytecode interpreter. The resulting `Proof` is
    verification-compatible with one from `prove`. Only valid when
    `system.toplevel` is the IxVM kernel's bytecode. -/
def proveIxVM (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Array G × Proof × IOBuffer :=
  let ioData := ioBuffer.data.toArray
  let ioMap := ioBuffer.map.toArray
  let (claim, proof, ioData, ioMap) := proveIxVM' system funIdx args
    ioData ioMap
  let ioData := ioData.foldl (fun acc (k, v) => acc.insert k v) ∅
  let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
  (claim, proof, ⟨ioData, ioMap⟩)

@[extern "rs_aiur_system_prove_addr_with_env"]
private opaque proveAddrWithEnv' : @& AiurSystem →
  @& Bytecode.FunIdx → @& EnvHandle → @& ByteArray →
    Except String (ByteArray × Proof ×
      Array (G × Array G) × Array ((G × Array G) × IOKeyInfo))

/-- Per-claim prove against a Rust-owned `EnvHandle`. Returns
    `(claimBytes, proof, ioBuffer)` — Rust serializes the
    reconstructed `Ix.Claim` via `ixon::Claim::put` so Lean can
    deserialize directly without re-running the closure walk. -/
def proveAddrWithEnv (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (envHandle : @& EnvHandle) (addrBytes : ByteArray) :
    Except String (ByteArray × Proof × IOBuffer) :=
  match proveAddrWithEnv' system funIdx envHandle addrBytes with
  | .error e => .error e
  | .ok (claimBytes, proof, ioData, ioMap) =>
    let ioData := ioData.foldl (fun acc (k, v) => acc.insert k v) ∅
    let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
    .ok (claimBytes, proof, ⟨ioData, ioMap⟩)

@[extern "rs_aiur_system_shard_prove_with_env"]
private opaque shardProveWithEnv' : @& AiurSystem →
  @& Bytecode.FunIdx → @& EnvHandle → @& ByteArray →
    Except String (ByteArray × Proof ×
      Array (G × Array G) × Array ((G × Array G) × IOKeyInfo))

/-- Per-shard prove against a Rust-owned `EnvHandle`. -/
def shardProveWithEnv (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (envHandle : @& EnvHandle) (ownedBlob : ByteArray) :
    Except String (ByteArray × Proof × IOBuffer) :=
  match shardProveWithEnv' system funIdx envHandle ownedBlob with
  | .error e => .error e
  | .ok (claimBytes, proof, ioData, ioMap) =>
    let ioData := ioData.foldl (fun acc (k, v) => acc.insert k v) ∅
    let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
    .ok (claimBytes, proof, ⟨ioData, ioMap⟩)

@[extern "rs_aiur_system_verify"]
opaque verify : @& AiurSystem →
  @& Array G → @& Proof → Except String Unit

end AiurSystem

abbrev functionChannel : G := .ofNat 0

def buildClaim (funIdx : Bytecode.FunIdx) (input output : Array G) :=
  #[functionChannel, .ofNat funIdx] ++ input ++ output

end Aiur

end
