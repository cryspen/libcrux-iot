namespace spec


-- Two ideas of how a Lean spec could look like:

def rotl64 (x : UInt64) (n: UInt32) : UInt64 :=
  if n == 0 || n == 64
  then x
  else (x <<< n.toUInt64) ||| (x >>> (64 - n.toUInt64))

def theta (state : Vector UInt64 25) : Vector UInt64 25 := Id.run do
  let mut c := Vector.replicate 5 (0 : UInt64)
  for h : x in [0:5] do
    c := c.set x (state[x]! ^^^ state[x + 5]! ^^^ state[x + 10]! ^^^ state[x + 15]! ^^^ state[x + 20]!)

  let mut d := Vector.replicate 5 (0 : UInt64)
  for h : x in [0:5] do
    d := d.set x (c[(x + 4) % 5] ^^^ rotl64 c[(x + 1) % 5] 1)

  let mut result := Vector.replicate 25 (0 : UInt64)
  for h : i in [0:25] do
    result := result.set i (state[i] ^^^ d[i % 5])

  result


namespace functional

def theta (state : Vector UInt64 25) : Vector UInt64 25 := Id.run do
  let c : Vector UInt64 5 :=
    .ofFn fun ⟨x, _⟩ =>
      state[x] ^^^ state[x + 5] ^^^ state[x + 10] ^^^ state[x + 15] ^^^ state[x + 20]

  let d : Vector UInt64 5 :=
    .ofFn fun ⟨x, _⟩ =>
      c[(x + 4) % 5] ^^^ rotl64 c[(x + 1) % 5] 1

  let result : Vector UInt64 25 :=
    .ofFn fun ⟨i, _⟩ =>
      state[i] ^^^ d[i % 5]

  result

end functional


end spec
