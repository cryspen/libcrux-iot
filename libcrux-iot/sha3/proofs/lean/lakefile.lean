import Lake
open Lake DSL

package libcrux_iot_sha3 where
  version := v!"0.1.0"

require Hax from git
  "https://github.com/cryspen/hax" @ "main" / "hax-lib" / "proof-libs" / "lean"

@[default_target]
lean_lib libcrux_iot_sha3 where
  roots := #[
    -- Shared helpers
    `keccak_verification.helpers,
    -- Reference specification (hacspec)
    `keccak_verification.spec.hacspec_sha3,
    `keccak_verification.spec.createi,
    -- Bit-interleaved implementation
    `keccak_verification.implementation.libcrux_iot_sha3,
    -- Equivalence proofs
    `keccak_verification.equivalence_proofs.lift_defs,
    `keccak_verification.equivalence_proofs.spec_decomp,
    `keccak_verification.equivalence_proofs.theta_lift,
    `keccak_verification.equivalence_proofs.prc_lift,
    `keccak_verification.equivalence_proofs.round_equiv_comp,
    `keccak_verification.equivalence_proofs.step_equiv,
    `keccak_verification.equivalence_proofs.equiv
  ]
