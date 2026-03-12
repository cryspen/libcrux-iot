import Lake
open Lake DSL

package «libcrux_iot_sha3» where
  version := v!"0.1.0"

@[default_target]
lean_lib «libcrux_iot_sha3» where
  roots := #[`extraction.libcrux_iot_sha3, `extraction.helpers]

require Hax from
  (s!"{get_config? haxHome |>.getD "../../hax/hax-lib/proof-libs/lean"}/hax-lib/proof-libs/lean" : System.FilePath)
