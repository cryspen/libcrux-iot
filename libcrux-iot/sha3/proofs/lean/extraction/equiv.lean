import extraction.hacspec_sha3
import extraction.libcrux_iot_sha3

#check hacspec_sha3.keccak_f.keccak_f
#check libcrux_iot_sha3.keccak.keccakf1600
def lift (s : libcrux_iot_sha3.state.KeccakState) : RustArray u64 25 :=
  RustArray.ofVec (.ofFn fun i =>
    UInt32.toUInt64 s.st.toVec[i]._0.toVec[0]
      ^^^ UInt32.toUInt64 s.st.toVec[i]._0.toVec[1] <<< 32)

theorem equivalence (s : libcrux_iot_sha3.state.KeccakState) :
  hacspec_sha3.keccak_f.keccak_f (lift s) =
    (do pure (lift (← libcrux_iot_sha3.keccak.keccakf1600 s))) := sorry
