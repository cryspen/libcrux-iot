"""
Generates Rust code of in-place interleaved SHA3 Keccak round functions.
"""

CONSTS_RC = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808a,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808b,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008a,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000a,
    0x0000_0000_8000_808b,
    0x8000_0000_0000_008b,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800a,
    0x8000_0000_8000_000a,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
]

def rc_i(i):
    return shuffle_bits(CONSTS_RC[i], 64)


def shuffle_bits(n: int, width: int = 64) -> int:
    """
    Shuffles the bits of an integer 'n' according to the pattern
    abcd...ABCD... -> aAbBcCdD...
    where a,b,c,d... are the bits of the upper half (most significant bits)
    and A,B,C,D... are the bits of the lower half (least significant bits).

    The function considers the lower 'width' bits of 'n'.

    Args:
        n: The integer number to shuffle.
        width: The bit width to consider for the number (must be a positive
               even integer). Defaults to 64.

    Returns:
        The integer with its lower 'width' bits shuffled according to the pattern.

    Raises:
        ValueError: If the width is not positive or not even.

    Example (8 bits):
        Input:  0b10110101 (a=1, b=0, c=1, d=1, A=0, B=1, C=0, D=1)
        Output: 0b10011011 (aAbBcCdD = 10 01 10 11)
    """
    # Validate the width argument
    if not isinstance(width, int) or width <= 0 or width % 2 != 0:
        raise ValueError("Width must be a positive even integer")

    half_width = width // 2
    result = 0

    # Create a mask to isolate the lower 'width' bits of the input number 'n'
    # This ensures that bits beyond the specified width do not affect the result.
    mask = (1 << width) - 1
    n &= mask

    # Iterate through the bit positions from the most significant side
    # 'i' represents the index within each half (0 to half_width - 1)
    for i in range(half_width):
        # --- Process the bit from the upper half ---
        # Calculate the index of the i-th bit (from MSB side) in the upper half
        # Example (width=8, half_width=4):
        # i=0 -> upper_bit_index = 8 - 1 - 0 = 7 (bit 'a')
        # i=1 -> upper_bit_index = 8 - 1 - 1 = 6 (bit 'b')
        upper_bit_index = width - 1 - i
        # Extract the bit value (0 or 1)
        upper_bit = (n >> upper_bit_index) & 1

        # Calculate the target index for this upper_bit in the result
        # It becomes the most significant bit of the i-th pair in the output
        # Example (width=8):
        # i=0 -> target_upper_index = 8 - 1 - 2*0 = 7
        # i=1 -> target_upper_index = 8 - 1 - 2*1 = 5
        target_upper_index = width - 1 - 2*i
        # Place the extracted bit at its target position in the result
        result |= (upper_bit << target_upper_index)

        # --- Process the bit from the lower half ---
        # Calculate the index of the i-th bit (from MSB side) in the lower half
        # Example (width=8, half_width=4):
        # i=0 -> lower_bit_index = 4 - 1 - 0 = 3 (bit 'A')
        # i=1 -> lower_bit_index = 4 - 1 - 1 = 2 (bit 'B')
        lower_bit_index = half_width - 1 - i
        # Extract the bit value (0 or 1)
        lower_bit = (n >> lower_bit_index) & 1

        # Calculate the target index for this lower_bit in the result
        # It becomes the least significant bit of the i-th pair in the output
        # Example (width=8):
        # i=0 -> target_lower_index = 8 - 2 - 2*0 = 6
        # i=1 -> target_lower_index = 8 - 2 - 2*1 = 4
        target_lower_index = width - 2 - 2*i
        # Place the extracted bit at its target position in the result
        result |= (lower_bit << target_lower_index)

    return result

# the y part of N^i . (x, y)
def ni_y(i, x, y):
    if i == 0:
        return y
    else:
        return ni_y(i-1, x, x + 2*y) % 5

# the y part of N^-i . (x, y)
def ninvi_y(i, x, y):
    if i == 0:
        return y
    else:
        return ninvi_y(i-1, x, 2*x + 3*y) %5

# r, as defined in the table early in the impl overview
def r(x, y):
    match (x, y):
        case (3, 2): return 25
        case (4, 2): return 39
        case (0, 2): return 3
        case (1, 2): return 10
        case (2, 2): return 43

        case (3, 1): return 55
        case (4, 1): return 20
        case (0, 1): return 36
        case (1, 1): return 44
        case (2, 1): return 6

        case (3, 0): return 28
        case (4, 0): return 27
        case (0, 0): return 0
        case (1, 0): return 1
        case (2, 0): return 62

        case (3, 4): return 56
        case (4, 4): return 14
        case (0, 4): return 18
        case (1, 4): return 2
        case (2, 4): return 61

        case (3, 3): return 21
        case (4, 3): return 8
        case (0, 3): return 41
        case (1, 3): return 45
        case (2, 3): return 15

# O(i, x, y), see p. 21
def big_o(i, x, y):
    if i %4 == 0:
        return 0

    return (-sum([r(x, ninvi_y(j, x, y)) for j in range(i)])) % 2

def cloop(i):
    def zeta_y(zeta, i, x, y):
        return (zeta + big_o(i, x, ni_y(i, x, y))) % 2

    out = ""
    for x in range(5):
        for zeta in range(2):
            out += "{\n"
            for y in range(5):
                zy = zeta_y(zeta, i, x, y)
                y_ni = ni_y(i,x, y)
                out += f"let ax_{y_ni} = s.get_with_zeta({y_ni}, {x}, {zy});\n"
            out += f"s.c[{x}][{zeta}] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;\n"
            out += "}\n"

    return out

def flatten(iterables):
    return (elem for iterable in iterables for elem in iterable)

def bloop_inner(i, y, zeta):
    def load(x):
        y_2prime = ni_y(i+1, x, y)
        rn = r(x, ni_y(1, x, y))
        zeta_prime = (zeta - rn) % 2 
        zeta_2prime = (zeta_prime + big_o(i, x, y_2prime)) % 2

        return f"""
        let a{x} = s.get_with_zeta({y_2prime},{x},{zeta_2prime});
        let d{x} = s.d[{x}][{zeta_2prime}];
        """

    def load_assign_stmt(x):
        y_2prime = ni_y(i+1, x, y)
        rn = r(x, ni_y(1, x, y))
        zeta_prime = (zeta - rn) % 2 
        zeta_2prime = (zeta_prime + big_o(i, x, y_2prime)) % 2

        return [
            f"let a{x} = s.get_with_zeta({y_2prime},{x},{zeta_2prime});",
            f"let d{x} = s.d[{x}][{zeta_prime}];"
        ]

    def compute(x):
        y_2prime = ni_y(i+1, x, y)
        rn = r(x, ni_y(1, x, y))
        zeta_prime = (zeta - rn) % 2 
        zeta_2prime = (zeta_prime + big_o(i, x, y_2prime)) % 2

        r_ =  rn//2 + 1 if  zeta < rn else rn//2 # // is integer division
        x_plus_2y = (x + 2 * y) % 5
        return f"let bx{x_plus_2y} = (a{x} ^ d{x}).rotate_left({r_});\n"

    def compute_expr(x):
        y_2prime = ni_y(i+1, x, y)
        rn = r(x, ni_y(1, x, y))
        zeta_prime = (zeta - rn) % 2 
        zeta_2prime = (zeta_prime + big_o(i, x, y_2prime)) % 2

        r_ =  rn//2 + 1 if  zeta < (rn %2) else rn//2 # // is integer division
        x_plus_2y = (x + 2 * y) % 5
        return f"(a{x} ^ d{x}).rotate_left({r_})"

    def as_tuple_str(exprs):
        out = "("
        delim = ""
        for expr in exprs:
            out += f"{delim}{expr}"
            delim = ", "
        out += ")"
        return out


    def joint_block(xrange):
        b_name= lambda x: f"bx{(x + 2 * y) % 5}"
        b_names = as_tuple_str(map(b_name, xrange))
        loads = "\n".join(flatten(map(load_assign_stmt, xrange)))
        comp_tuple = as_tuple_str(map(compute_expr, xrange))

        return f"let {b_names} = {{\n {loads}\n {comp_tuple}\n }};\n"

    break_at = 2
    return joint_block(range(break_at)) + joint_block(range(break_at, 5))


def aloop_inner(i, y, zeta):
    def avar(x):
        return f"ax{x}"

    def bvar(x):
        return f"bx{x}"

    def load(x):
        return f"let bx{x} = b[{x}];\n"

    def compute(x):
        x_plus_one = (x + 1) % 5
        x_plus_two = (x + 2) % 5
        y_2prime = ni_y(i+1,x, y)

        # This is the actual expresion, but sometimes we want to also xor round
        # constants to it.
        base_expr = f"{bvar(x)} ^ ((! {bvar(x_plus_one)}) & {bvar(x_plus_two)})"

        # In this case we'll need to add the round constants. In the algorithm
        # it is done at the very end, but it is more efficient to do it now,
        # because we don't need to load and store again.
        if y_2prime == 0 and x == 0:
            zeta_plus_o = (zeta + big_o(i+1, x, y_2prime)) % 2
            rc_name = f"RC_INTERLEAVED_{zeta_plus_o}"

            # if zeta is one, which is always the second and last time we
            # access the round constants and need i, update the i stored in
            # the state.
            maybe_update_i = "s.i = i + 1;" if zeta_plus_o == 1 else ""

            return f"""let {avar(x)};
            #[cfg(feature = "full-unroll")]
            {{
                {avar(x)} = {base_expr} ^ {rc_name}[BASE_ROUND + {i}];
            }};
            #[cfg(not(feature = "full-unroll"))]
            {{
                {avar(x)} = {base_expr} ^ {rc_name}[i];
                {maybe_update_i}
            }};
            """
        else:
            return f"let {avar(x)} = {base_expr};\n"

    def store(x):
        y_2prime = ni_y(i+1,x, y)
        zeta_plus_o = (zeta + big_o(i+1, x, y_2prime)) % 2
        return f"s.set_with_zeta({y_2prime}, {x}, {zeta_plus_o}, {avar(x)});\n"

    out = ""
    for x in range(5):
        out += compute(x)
        out += store(x)

    return out

def abloop(i):
    out = ""
    break_at = 2
    for y in range(5):
        for zeta in range(2):
            out += "{\n"
            out += bloop_inner(i, y, zeta)
            out += aloop_inner(i, y, zeta)
            out += "}\n"


    return out

def dloop(i):
    def cvar(x, zeta):
        return f"c_x{x}_zeta{zeta}"

    def dvar(x, zeta):
        return f"d_x{x}_zeta{zeta}"

    def load(x, zeta):
        return f"let {cvar(x, zeta)} = s.c[{x}][{zeta}];\n"

    def compute(x, zeta):
        x_minus_one = (x - 1) % 5
        x_plus_one = (x + 1) % 5
        rotate_call = "" if zeta == 1 else ".rotate_left(1)"
        return f"let {dvar(x, zeta)} = {cvar(x_minus_one, zeta)} ^ {cvar(x_plus_one, 1-zeta)}{rotate_call};\n"

    def store(x, zeta):
        return f"s.d[{x}][{zeta}] = {dvar(x, zeta)};\n"

    ld_order = [(4,0),(1,1), (3,0), (0,1), (2,0), (4,1), (1,0), (3,1),(2,1), (0,0)];
    comp_order = [(0,0), (2,1), (4,0), (1,1), (3,0), (0,1), (2,0), (4,1 ), (1,0), (3,1)]

    out = "{\n"

    for j in range(6):
        (x, zeta) = ld_order[j]
        out += load(x, zeta)

    for j in range(5):
        (x, zeta) = comp_order[j]
        out += compute(x, zeta)
        out += store(x, zeta)

    for j in range(6, 10):
        (x, zeta) = ld_order[j]
        out += load(x, zeta)

    for j in range(5, 10):
        (x, zeta) = comp_order[j]
        out += compute(x, zeta)
        out += store(x, zeta)

    out += "}\n"
    return out

    

def round(i):
    out = ""
    out += cloop(i)
    out += dloop(i)
    out += """#[cfg(not(feature = "full-unroll"))]
    let i = s.i;
    """
    out += abloop(i)
    return out


def defn_roundfn(i):
    return f"""
#[inline(always)]
    pub(crate) fn keccakf1600_round{i}<const BASE_ROUND: usize>(s: &mut KeccakState) {{
        {round(i)}
    }}
    """

for i in range(4):
    print(defn_roundfn(i))

