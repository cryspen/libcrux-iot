import Lake
open Lake DSL

package libcrux_iot_sha3 where
  version := v!"0.1.0"

require Hax from git
  "https://github.com/cryspen/hax" @ "main" / "hax-lib" / "proof-libs" / "lean"

lean_lib libcrux_iot_sha3 where
  roots := #[`extraction.equiv, `extraction.step_equiv, `extraction.step_equiv_extras, `extraction.round_equiv, `extraction.spec, `extraction.helpers, `extraction.hacspec_sha3, `extraction.libcrux_iot_sha3]
