macro_rules! print_state {
    ($s:expr, $c:expr, $d:expr) => {
        println!("A:");
        println!("{s}", s = $s);
        println!("C:");
        println!("{c}", c = slice_to_string(&$c));
        println!("D:");
        println!("{d}", d = slice_to_string(&$d));
    };
}

#[test]
fn keccak_4rounds_print() {
    let mut s = libcrux_sha3::portable::incremental::shake128_init();
    libcrux_sha3::portable::incremental::keccakf1660_4rounds(&mut s);
    println!("{s:?}")
}

#[test]
fn keccak_print_rounds0123() {
    let mut s = State::default();
    let mut c = [[0u32; 2]; 5];
    let mut d = [[0u32; 2]; 5];
    s.keccak_round0(&mut c, &mut d, 0);
    s.keccak_round1(&mut c, &mut d, 0);
    s.keccak_round2(&mut c, &mut d, 0);
    s.keccak_round3(&mut c, &mut d, 0);
    print_state!(s, c, d);
}

#[test]
fn keccak_print_24rounds() {
    let mut s = State::default();
    let mut c = [[0u32; 2]; 5];
    let mut d = [[0u32; 2]; 5];

    for i in 0..6 {
        s.keccak_round0(&mut c, &mut d, i);
        s.keccak_round1(&mut c, &mut d, i);
        s.keccak_round2(&mut c, &mut d, i);
        s.keccak_round3(&mut c, &mut d, i);
    }
    print_state!(s, c, d);
}

#[derive(Debug, Default)]
struct State([[u32; 2]; 25]);

impl From<[[u32; 2]; 25]> for State {
    fn from(value: [[u32; 2]; 25]) -> Self {
        Self(value)
    }
}

fn slice_to_string(slice: &[[u32; 2]; 5]) -> String {
    let mut str = String::with_capacity(40);
    format_slice(&mut str, slice).unwrap();
    str
}

fn format_slice<W: std::fmt::Write>(w: &mut W, slice: &[[u32; 2]; 5]) -> std::fmt::Result {
    let a0 = slice[0][0];
    let a1 = slice[0][1];
    let e0 = slice[1][0];
    let e1 = slice[1][1];
    let i0 = slice[2][0];
    let i1 = slice[2][1];
    let o0 = slice[3][0];
    let o1 = slice[3][1];
    let u0 = slice[4][0];
    let u1 = slice[4][1];

    write!(w, "{a0} {e0} {i0} {o0} {u0}\n")?;
    write!(w, "{a1} {e1} {i1} {o1} {u1}\n")
}

impl std::fmt::Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for y in 0..5 {
            format_slice(f, &self.0[5 * y..5 * (y + 1)].try_into().unwrap())?;
        }

        Ok(())
    }
}

impl State {
    fn get_with_zeta(&self, y: usize, x: usize, zeta: usize) -> u32 {
        self.0[5 * y + x][zeta]
    }

    fn set_with_zeta(&mut self, y: usize, x: usize, zeta: usize, v: u32) {
        self.0[5 * y + x][zeta] = v
    }

    fn keccak_round0_cloop(&mut self, c: &mut [[u32; 2]; 5], d: &mut [[u32; 2]; 5]) {
        let i = 0;

        {
            let ax_0 = self.get_with_zeta(0, 0, 0);
            let ax_1 = self.get_with_zeta(1, 0, 0);
            let ax_2 = self.get_with_zeta(2, 0, 0);
            let ax_3 = self.get_with_zeta(3, 0, 0);
            let ax_4 = self.get_with_zeta(4, 0, 0);
            c[0][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_0 = self.get_with_zeta(0, 0, 1);
            let ax_1 = self.get_with_zeta(1, 0, 1);
            let ax_2 = self.get_with_zeta(2, 0, 1);
            let ax_3 = self.get_with_zeta(3, 0, 1);
            let ax_4 = self.get_with_zeta(4, 0, 1);
            c[0][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_0 = self.get_with_zeta(0, 1, 0);
            let ax_1 = self.get_with_zeta(1, 1, 0);
            let ax_2 = self.get_with_zeta(2, 1, 0);
            let ax_3 = self.get_with_zeta(3, 1, 0);
            let ax_4 = self.get_with_zeta(4, 1, 0);
            c[1][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_0 = self.get_with_zeta(0, 1, 1);
            let ax_1 = self.get_with_zeta(1, 1, 1);
            let ax_2 = self.get_with_zeta(2, 1, 1);
            let ax_3 = self.get_with_zeta(3, 1, 1);
            let ax_4 = self.get_with_zeta(4, 1, 1);
            c[1][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_0 = self.get_with_zeta(0, 2, 0);
            let ax_1 = self.get_with_zeta(1, 2, 0);
            let ax_2 = self.get_with_zeta(2, 2, 0);
            let ax_3 = self.get_with_zeta(3, 2, 0);
            let ax_4 = self.get_with_zeta(4, 2, 0);
            c[2][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_0 = self.get_with_zeta(0, 2, 1);
            let ax_1 = self.get_with_zeta(1, 2, 1);
            let ax_2 = self.get_with_zeta(2, 2, 1);
            let ax_3 = self.get_with_zeta(3, 2, 1);
            let ax_4 = self.get_with_zeta(4, 2, 1);
            c[2][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_0 = self.get_with_zeta(0, 3, 0);
            let ax_1 = self.get_with_zeta(1, 3, 0);
            let ax_2 = self.get_with_zeta(2, 3, 0);
            let ax_3 = self.get_with_zeta(3, 3, 0);
            let ax_4 = self.get_with_zeta(4, 3, 0);
            c[3][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_0 = self.get_with_zeta(0, 3, 1);
            let ax_1 = self.get_with_zeta(1, 3, 1);
            let ax_2 = self.get_with_zeta(2, 3, 1);
            let ax_3 = self.get_with_zeta(3, 3, 1);
            let ax_4 = self.get_with_zeta(4, 3, 1);
            c[3][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_0 = self.get_with_zeta(0, 4, 0);
            let ax_1 = self.get_with_zeta(1, 4, 0);
            let ax_2 = self.get_with_zeta(2, 4, 0);
            let ax_3 = self.get_with_zeta(3, 4, 0);
            let ax_4 = self.get_with_zeta(4, 4, 0);
            c[4][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_0 = self.get_with_zeta(0, 4, 1);
            let ax_1 = self.get_with_zeta(1, 4, 1);
            let ax_2 = self.get_with_zeta(2, 4, 1);
            let ax_3 = self.get_with_zeta(3, 4, 1);
            let ax_4 = self.get_with_zeta(4, 4, 1);
            c[4][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
    }

    fn keccak_round0_dloop(&mut self, c: &mut [[u32; 2]; 5], d: &mut [[u32; 2]; 5]) {
        let i = 0;

        {
            let c_x4_zeta0 = c[4][0];

            let c_x1_zeta1 = c[1][1];

            let c_x3_zeta0 = c[3][0];

            let c_x0_zeta1 = c[0][1];

            let c_x2_zeta0 = c[2][0];

            let c_x4_zeta1 = c[4][1];

            let d_x0_zeta0 = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
            d[0][0] = d_x0_zeta0;
            let d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
            d[2][1] = d_x2_zeta1;
            let d_x4_zeta0 = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
            d[4][0] = d_x4_zeta0;
            let d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
            d[1][1] = d_x1_zeta1;
            let d_x3_zeta0 = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
            d[3][0] = d_x3_zeta0;
            let c_x1_zeta0 = c[1][0];

            let c_x3_zeta1 = c[3][1];

            let c_x2_zeta1 = c[2][1];

            let c_x0_zeta0 = c[0][0];

            let d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
            d[0][1] = d_x0_zeta1;
            let d_x2_zeta0 = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
            d[2][0] = d_x2_zeta0;
            let d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
            d[4][1] = d_x4_zeta1;
            let d_x1_zeta0 = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
            d[1][0] = d_x1_zeta0;
            let d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
            d[3][1] = d_x3_zeta1;
        }
    }

    fn keccak_round0(&mut self, c: &mut [[u32; 2]; 5], d: &mut [[u32; 2]; 5], i: usize) {
        self.keccak_round0_cloop(c, d);
        self.keccak_round0_dloop(c, d);
        {
            let (bx0, bx1) = {
                let a0 = self.get_with_zeta(0, 0, 0);
                let d0 = d[0][0];
                let a1 = self.get_with_zeta(1, 1, 0);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
            };
            let (bx2, bx3, bx4) = {
                let a2 = self.get_with_zeta(2, 2, 1);
                let d2 = d[2][1];
                let a3 = self.get_with_zeta(3, 3, 1);
                let d3 = d[3][1];
                let a4 = self.get_with_zeta(4, 4, 0);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(22),
                    (a3 ^ d3).rotate_left(11),
                    (a4 ^ d4).rotate_left(7),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            self.set_with_zeta(0, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            self.set_with_zeta(1, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            self.set_with_zeta(2, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            self.set_with_zeta(3, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            self.set_with_zeta(4, 4, 0, ax4);
        }
        {
            let (bx0, bx1) = {
                let a0 = self.get_with_zeta(0, 0, 1);
                let d0 = d[0][1];
                let a1 = self.get_with_zeta(1, 1, 1);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
            };
            let (bx2, bx3, bx4) = {
                let a2 = self.get_with_zeta(2, 2, 0);
                let d2 = d[2][0];
                let a3 = self.get_with_zeta(3, 3, 0);
                let d3 = d[3][0];
                let a4 = self.get_with_zeta(4, 4, 1);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(21),
                    (a3 ^ d3).rotate_left(10),
                    (a4 ^ d4).rotate_left(7),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            self.set_with_zeta(0, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            self.set_with_zeta(1, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            self.set_with_zeta(2, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            self.set_with_zeta(3, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            self.set_with_zeta(4, 4, 1, ax4);
        }
        {
            let (bx2, bx3) = {
                let a0 = self.get_with_zeta(2, 0, 1);
                let d0 = d[0][1];
                let a1 = self.get_with_zeta(3, 1, 1);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(2), (a1 ^ d1).rotate_left(23))
            };
            let (bx4, bx0, bx1) = {
                let a2 = self.get_with_zeta(4, 2, 1);
                let d2 = d[2][1];
                let a3 = self.get_with_zeta(0, 3, 0);
                let d3 = d[3][0];
                let a4 = self.get_with_zeta(1, 4, 0);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(31),
                    (a3 ^ d3).rotate_left(14),
                    (a4 ^ d4).rotate_left(10),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            self.set_with_zeta(2, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            self.set_with_zeta(3, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            self.set_with_zeta(4, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            self.set_with_zeta(0, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            self.set_with_zeta(1, 4, 0, ax4);
        }
        {
            let (bx2, bx3) = {
                let a0 = self.get_with_zeta(2, 0, 0);
                let d0 = d[0][0];
                let a1 = self.get_with_zeta(3, 1, 0);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(1), (a1 ^ d1).rotate_left(22))
            };
            let (bx4, bx0, bx1) = {
                let a2 = self.get_with_zeta(4, 2, 0);
                let d2 = d[2][0];
                let a3 = self.get_with_zeta(0, 3, 1);
                let d3 = d[3][1];
                let a4 = self.get_with_zeta(1, 4, 1);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(30),
                    (a3 ^ d3).rotate_left(14),
                    (a4 ^ d4).rotate_left(10),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            self.set_with_zeta(2, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            self.set_with_zeta(3, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            self.set_with_zeta(4, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            self.set_with_zeta(0, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            self.set_with_zeta(1, 4, 1, ax4);
        }
        {
            let (bx4, bx0) = {
                let a0 = self.get_with_zeta(4, 0, 0);
                let d0 = d[0][0];
                let a1 = self.get_with_zeta(0, 1, 1);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(1))
            };
            let (bx1, bx2, bx3) = {
                let a2 = self.get_with_zeta(1, 2, 0);
                let d2 = d[2][0];
                let a3 = self.get_with_zeta(2, 3, 1);
                let d3 = d[3][1];
                let a4 = self.get_with_zeta(3, 4, 0);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(3),
                    (a3 ^ d3).rotate_left(13),
                    (a4 ^ d4).rotate_left(4),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            self.set_with_zeta(4, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            self.set_with_zeta(0, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            self.set_with_zeta(1, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            self.set_with_zeta(2, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            self.set_with_zeta(3, 4, 0, ax4);
        }
        {
            let (bx4, bx0) = {
                let a0 = self.get_with_zeta(4, 0, 1);
                let d0 = d[0][1];
                let a1 = self.get_with_zeta(0, 1, 0);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(0))
            };
            let (bx1, bx2, bx3) = {
                let a2 = self.get_with_zeta(1, 2, 1);
                let d2 = d[2][1];
                let a3 = self.get_with_zeta(2, 3, 0);
                let d3 = d[3][0];
                let a4 = self.get_with_zeta(3, 4, 1);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(3),
                    (a3 ^ d3).rotate_left(12),
                    (a4 ^ d4).rotate_left(4),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            self.set_with_zeta(4, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            self.set_with_zeta(0, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            self.set_with_zeta(1, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            self.set_with_zeta(2, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            self.set_with_zeta(3, 4, 1, ax4);
        }
        {
            let (bx1, bx2) = {
                let a0 = self.get_with_zeta(1, 0, 0);
                let d0 = d[0][0];
                let a1 = self.get_with_zeta(2, 1, 0);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
            };
            let (bx3, bx4, bx0) = {
                let a2 = self.get_with_zeta(3, 2, 1);
                let d2 = d[2][1];
                let a3 = self.get_with_zeta(4, 3, 0);
                let d3 = d[3][0];
                let a4 = self.get_with_zeta(0, 4, 1);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(8),
                    (a3 ^ d3).rotate_left(28),
                    (a4 ^ d4).rotate_left(14),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            self.set_with_zeta(1, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            self.set_with_zeta(2, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            self.set_with_zeta(3, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            self.set_with_zeta(4, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            self.set_with_zeta(0, 4, 1, ax4);
        }
        {
            let (bx1, bx2) = {
                let a0 = self.get_with_zeta(1, 0, 1);
                let d0 = d[0][1];
                let a1 = self.get_with_zeta(2, 1, 1);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
            };
            let (bx3, bx4, bx0) = {
                let a2 = self.get_with_zeta(3, 2, 0);
                let d2 = d[2][0];
                let a3 = self.get_with_zeta(4, 3, 1);
                let d3 = d[3][1];
                let a4 = self.get_with_zeta(0, 4, 0);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(7),
                    (a3 ^ d3).rotate_left(28),
                    (a4 ^ d4).rotate_left(13),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            self.set_with_zeta(1, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            self.set_with_zeta(2, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            self.set_with_zeta(3, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            self.set_with_zeta(4, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            self.set_with_zeta(0, 4, 0, ax4);
        }
        {
            let (bx3, bx4) = {
                let a0 = self.get_with_zeta(3, 0, 1);
                let d0 = d[0][1];
                let a1 = self.get_with_zeta(4, 1, 0);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(21), (a1 ^ d1).rotate_left(1))
            };
            let (bx0, bx1, bx2) = {
                let a2 = self.get_with_zeta(0, 2, 0);
                let d2 = d[2][0];
                let a3 = self.get_with_zeta(1, 3, 1);
                let d3 = d[3][1];
                let a4 = self.get_with_zeta(2, 4, 1);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(31),
                    (a3 ^ d3).rotate_left(28),
                    (a4 ^ d4).rotate_left(20),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            self.set_with_zeta(3, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            self.set_with_zeta(4, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            self.set_with_zeta(0, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            self.set_with_zeta(1, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            self.set_with_zeta(2, 4, 1, ax4);
        }
        {
            let (bx3, bx4) = {
                let a0 = self.get_with_zeta(3, 0, 0);
                let d0 = d[0][0];
                let a1 = self.get_with_zeta(4, 1, 1);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(20), (a1 ^ d1).rotate_left(1))
            };
            let (bx0, bx1, bx2) = {
                let a2 = self.get_with_zeta(0, 2, 1);
                let d2 = d[2][1];
                let a3 = self.get_with_zeta(1, 3, 0);
                let d3 = d[3][0];
                let a4 = self.get_with_zeta(2, 4, 0);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(31),
                    (a3 ^ d3).rotate_left(27),
                    (a4 ^ d4).rotate_left(19),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            self.set_with_zeta(3, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            self.set_with_zeta(4, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            self.set_with_zeta(0, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            self.set_with_zeta(1, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            self.set_with_zeta(2, 4, 0, ax4);
        }
        let az0 = self.get_with_zeta(0, 0, 0);
        let az1 = self.get_with_zeta(0, 0, 1);
        self.set_with_zeta(0, 0, 0, az0 ^ RC_INTERLEAVED_0[i]);
        self.set_with_zeta(0, 0, 1, az1 ^ RC_INTERLEAVED_1[i]);
    }

    fn keccak_round1_cloop(&mut self, c: &mut [[u32; 2]; 5], d: &mut [[u32; 2]; 5]) {
        let s = self;

        {
            let ax_0 = s.get_with_zeta(0, 0, 0);
            let ax_2 = s.get_with_zeta(2, 0, 1);
            let ax_4 = s.get_with_zeta(4, 0, 0);
            let ax_1 = s.get_with_zeta(1, 0, 0);
            let ax_3 = s.get_with_zeta(3, 0, 1);
            c[0][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_0 = s.get_with_zeta(0, 0, 1);
            let ax_2 = s.get_with_zeta(2, 0, 0);
            let ax_4 = s.get_with_zeta(4, 0, 1);
            let ax_1 = s.get_with_zeta(1, 0, 1);
            let ax_3 = s.get_with_zeta(3, 0, 0);
            c[0][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_1 = s.get_with_zeta(1, 1, 0);
            let ax_3 = s.get_with_zeta(3, 1, 1);
            let ax_0 = s.get_with_zeta(0, 1, 1);
            let ax_2 = s.get_with_zeta(2, 1, 0);
            let ax_4 = s.get_with_zeta(4, 1, 0);
            c[1][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_1 = s.get_with_zeta(1, 1, 1);
            let ax_3 = s.get_with_zeta(3, 1, 0);
            let ax_0 = s.get_with_zeta(0, 1, 0);
            let ax_2 = s.get_with_zeta(2, 1, 1);
            let ax_4 = s.get_with_zeta(4, 1, 1);
            c[1][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_2 = s.get_with_zeta(2, 2, 1);
            let ax_4 = s.get_with_zeta(4, 2, 1);
            let ax_1 = s.get_with_zeta(1, 2, 0);
            let ax_3 = s.get_with_zeta(3, 2, 1);
            let ax_0 = s.get_with_zeta(0, 2, 0);
            c[2][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_2 = s.get_with_zeta(2, 2, 0);
            let ax_4 = s.get_with_zeta(4, 2, 0);
            let ax_1 = s.get_with_zeta(1, 2, 1);
            let ax_3 = s.get_with_zeta(3, 2, 0);
            let ax_0 = s.get_with_zeta(0, 2, 1);
            c[2][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_3 = s.get_with_zeta(3, 3, 1);
            let ax_0 = s.get_with_zeta(0, 3, 0);
            let ax_2 = s.get_with_zeta(2, 3, 1);
            let ax_4 = s.get_with_zeta(4, 3, 0);
            let ax_1 = s.get_with_zeta(1, 3, 1);
            c[3][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_3 = s.get_with_zeta(3, 3, 0);
            let ax_0 = s.get_with_zeta(0, 3, 1);
            let ax_2 = s.get_with_zeta(2, 3, 0);
            let ax_4 = s.get_with_zeta(4, 3, 1);
            let ax_1 = s.get_with_zeta(1, 3, 0);
            c[3][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_4 = s.get_with_zeta(4, 4, 0);
            let ax_1 = s.get_with_zeta(1, 4, 0);
            let ax_3 = s.get_with_zeta(3, 4, 0);
            let ax_0 = s.get_with_zeta(0, 4, 1);
            let ax_2 = s.get_with_zeta(2, 4, 1);
            c[4][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_4 = s.get_with_zeta(4, 4, 1);
            let ax_1 = s.get_with_zeta(1, 4, 1);
            let ax_3 = s.get_with_zeta(3, 4, 1);
            let ax_0 = s.get_with_zeta(0, 4, 0);
            let ax_2 = s.get_with_zeta(2, 4, 0);
            c[4][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
    }

    fn keccak_round1_dloop(&mut self, c: &mut [[u32; 2]; 5], d: &mut [[u32; 2]; 5]) {
        let c_x4_zeta0 = c[4][0];
        let c_x1_zeta1 = c[1][1];
        let c_x3_zeta0 = c[3][0];
        let c_x0_zeta1 = c[0][1];
        let c_x2_zeta0 = c[2][0];
        let c_x4_zeta1 = c[4][1];
        let d_x0_zeta0 = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
        d[0][0] = d_x0_zeta0;
        let d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
        d[2][1] = d_x2_zeta1;
        let d_x4_zeta0 = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
        d[4][0] = d_x4_zeta0;
        let d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
        d[1][1] = d_x1_zeta1;
        let d_x3_zeta0 = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
        d[3][0] = d_x3_zeta0;
        let c_x1_zeta0 = c[1][0];
        let c_x3_zeta1 = c[3][1];
        let c_x2_zeta1 = c[2][1];
        let c_x0_zeta0 = c[0][0];
        let d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
        d[0][1] = d_x0_zeta1;
        let d_x2_zeta0 = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
        d[2][0] = d_x2_zeta0;
        let d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
        d[4][1] = d_x4_zeta1;
        let d_x1_zeta0 = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
        d[1][0] = d_x1_zeta0;
        let d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
        d[3][1] = d_x3_zeta1;
    }

    fn keccak_round1_abloop(&mut self, c: &mut [[u32; 2]; 5], d: &mut [[u32; 2]; 5], i: usize) {
        let s = self;

        {
            let (bx0, bx1) = {
                let a0 = s.get_with_zeta(0, 0, 0);
                let d0 = d[0][0];
                let a1 = s.get_with_zeta(3, 1, 1);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
            };
            let (bx2, bx3, bx4) = {
                let a2 = s.get_with_zeta(1, 2, 1);
                let d2 = d[2][1];
                let a3 = s.get_with_zeta(4, 3, 1);
                let d3 = d[3][1];
                let a4 = s.get_with_zeta(2, 4, 1);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(22),
                    (a3 ^ d3).rotate_left(11),
                    (a4 ^ d4).rotate_left(7),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(0, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(3, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(1, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(4, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(2, 4, 1, ax4);
        }
        {
            let (bx0, bx1) = {
                let a0 = s.get_with_zeta(0, 0, 1);
                let d0 = d[0][1];
                let a1 = s.get_with_zeta(3, 1, 0);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
            };
            let (bx2, bx3, bx4) = {
                let a2 = s.get_with_zeta(1, 2, 0);
                let d2 = d[2][0];
                let a3 = s.get_with_zeta(4, 3, 0);
                let d3 = d[3][0];
                let a4 = s.get_with_zeta(2, 4, 0);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(21),
                    (a3 ^ d3).rotate_left(10),
                    (a4 ^ d4).rotate_left(7),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(0, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(3, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(1, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(4, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(2, 4, 0, ax4);
        }
        {
            let (bx2, bx3) = {
                let a0 = s.get_with_zeta(4, 0, 1);
                let d0 = d[0][1];
                let a1 = s.get_with_zeta(2, 1, 1);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(2), (a1 ^ d1).rotate_left(23))
            };
            let (bx4, bx0, bx1) = {
                let a2 = s.get_with_zeta(0, 2, 1);
                let d2 = d[2][1];
                let a3 = s.get_with_zeta(3, 3, 1);
                let d3 = d[3][0];
                let a4 = s.get_with_zeta(1, 4, 0);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(31),
                    (a3 ^ d3).rotate_left(14),
                    (a4 ^ d4).rotate_left(10),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(4, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(2, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(0, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(3, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(1, 4, 0, ax4);
        }
        {
            let (bx2, bx3) = {
                let a0 = s.get_with_zeta(4, 0, 0);
                let d0 = d[0][0];
                let a1 = s.get_with_zeta(2, 1, 0);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(1), (a1 ^ d1).rotate_left(22))
            };
            let (bx4, bx0, bx1) = {
                let a2 = s.get_with_zeta(0, 2, 0);
                let d2 = d[2][0];
                let a3 = s.get_with_zeta(3, 3, 0);
                let d3 = d[3][1];
                let a4 = s.get_with_zeta(1, 4, 1);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(30),
                    (a3 ^ d3).rotate_left(14),
                    (a4 ^ d4).rotate_left(10),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(4, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(2, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(0, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(3, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(1, 4, 1, ax4);
        }
        {
            let (bx4, bx0) = {
                let a0 = s.get_with_zeta(3, 0, 1);
                let d0 = d[0][0];
                let a1 = s.get_with_zeta(1, 1, 1);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(1))
            };
            let (bx1, bx2, bx3) = {
                let a2 = s.get_with_zeta(4, 2, 1);
                let d2 = d[2][0];
                let a3 = s.get_with_zeta(2, 3, 0);
                let d3 = d[3][1];
                let a4 = s.get_with_zeta(0, 4, 1);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(3),
                    (a3 ^ d3).rotate_left(13),
                    (a4 ^ d4).rotate_left(4),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(3, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(1, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(4, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(2, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(0, 4, 1, ax4);
        }
        {
            let (bx4, bx0) = {
                let a0 = s.get_with_zeta(3, 0, 0);
                let d0 = d[0][1];
                let a1 = s.get_with_zeta(1, 1, 0);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(0))
            };
            let (bx1, bx2, bx3) = {
                let a2 = s.get_with_zeta(4, 2, 0);
                let d2 = d[2][1];
                let a3 = s.get_with_zeta(2, 3, 1);
                let d3 = d[3][0];
                let a4 = s.get_with_zeta(0, 4, 0);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(3),
                    (a3 ^ d3).rotate_left(12),
                    (a4 ^ d4).rotate_left(4),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(3, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(1, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(4, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(2, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(0, 4, 0, ax4);
        }
        {
            let (bx1, bx2) = {
                let a0 = s.get_with_zeta(2, 0, 1);
                let d0 = d[0][0];
                let a1 = s.get_with_zeta(0, 1, 1);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
            };
            let (bx3, bx4, bx0) = {
                let a2 = s.get_with_zeta(3, 2, 0);
                let d2 = d[2][1];
                let a3 = s.get_with_zeta(1, 3, 1);
                let d3 = d[3][0];
                let a4 = s.get_with_zeta(4, 4, 1);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(8),
                    (a3 ^ d3).rotate_left(28),
                    (a4 ^ d4).rotate_left(14),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(2, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(0, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(3, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(1, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(4, 4, 1, ax4);
        }
        {
            let (bx1, bx2) = {
                let a0 = s.get_with_zeta(2, 0, 0);
                let d0 = d[0][1];
                let a1 = s.get_with_zeta(0, 1, 0);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
            };
            let (bx3, bx4, bx0) = {
                let a2 = s.get_with_zeta(3, 2, 1);
                let d2 = d[2][0];
                let a3 = s.get_with_zeta(1, 3, 0);
                let d3 = d[3][1];
                let a4 = s.get_with_zeta(4, 4, 0);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(7),
                    (a3 ^ d3).rotate_left(28),
                    (a4 ^ d4).rotate_left(13),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(2, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(0, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(3, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(1, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(4, 4, 0, ax4);
        }
        {
            let (bx3, bx4) = {
                let a0 = s.get_with_zeta(1, 0, 1);
                let d0 = d[0][1];
                let a1 = s.get_with_zeta(4, 1, 0);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(21), (a1 ^ d1).rotate_left(1))
            };
            let (bx0, bx1, bx2) = {
                let a2 = s.get_with_zeta(2, 2, 1);
                let d2 = d[2][0];
                let a3 = s.get_with_zeta(0, 3, 1);
                let d3 = d[3][1];
                let a4 = s.get_with_zeta(3, 4, 1);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(31),
                    (a3 ^ d3).rotate_left(28),
                    (a4 ^ d4).rotate_left(20),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(1, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(4, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(2, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(0, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(3, 4, 1, ax4);
        }
        {
            let (bx3, bx4) = {
                let a0 = s.get_with_zeta(1, 0, 0);
                let d0 = d[0][0];
                let a1 = s.get_with_zeta(4, 1, 1);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(20), (a1 ^ d1).rotate_left(1))
            };
            let (bx0, bx1, bx2) = {
                let a2 = s.get_with_zeta(2, 2, 0);
                let d2 = d[2][1];
                let a3 = s.get_with_zeta(0, 3, 0);
                let d3 = d[3][0];
                let a4 = s.get_with_zeta(3, 4, 0);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(31),
                    (a3 ^ d3).rotate_left(27),
                    (a4 ^ d4).rotate_left(19),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(1, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(4, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(2, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(0, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(3, 4, 0, ax4);
        }
        let az0 = s.get_with_zeta(0, 0, 0);
        let az1 = s.get_with_zeta(0, 0, 1);
        s.set_with_zeta(0, 0, 0, az0 ^ RC_INTERLEAVED_0[i + 1]);
        s.set_with_zeta(0, 0, 1, az1 ^ RC_INTERLEAVED_1[i + 1]);
    }

    fn keccak_round1(&mut self, c: &mut [[u32; 2]; 5], d: &mut [[u32; 2]; 5], i: usize) {
        self.keccak_round1_cloop(c, d);
        self.keccak_round1_dloop(c, d);
        self.keccak_round1_abloop(c, d, i);
    }

    fn keccak_round2(&mut self, c: &mut [[u32; 2]; 5], d: &mut [[u32; 2]; 5], i: usize) {
        let s = self;

        {
            let ax_0 = s.get_with_zeta(0, 0, 0);
            let ax_4 = s.get_with_zeta(4, 0, 1);
            let ax_3 = s.get_with_zeta(3, 0, 1);
            let ax_2 = s.get_with_zeta(2, 0, 1);
            let ax_1 = s.get_with_zeta(1, 0, 1);
            c[0][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_0 = s.get_with_zeta(0, 0, 1);
            let ax_4 = s.get_with_zeta(4, 0, 0);
            let ax_3 = s.get_with_zeta(3, 0, 0);
            let ax_2 = s.get_with_zeta(2, 0, 0);
            let ax_1 = s.get_with_zeta(1, 0, 0);
            c[0][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_3 = s.get_with_zeta(3, 1, 1);
            let ax_2 = s.get_with_zeta(2, 1, 1);
            let ax_1 = s.get_with_zeta(1, 1, 1);
            let ax_0 = s.get_with_zeta(0, 1, 1);
            let ax_4 = s.get_with_zeta(4, 1, 0);
            c[1][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_3 = s.get_with_zeta(3, 1, 0);
            let ax_2 = s.get_with_zeta(2, 1, 0);
            let ax_1 = s.get_with_zeta(1, 1, 0);
            let ax_0 = s.get_with_zeta(0, 1, 0);
            let ax_4 = s.get_with_zeta(4, 1, 1);
            c[1][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_1 = s.get_with_zeta(1, 2, 1);
            let ax_0 = s.get_with_zeta(0, 2, 1);
            let ax_4 = s.get_with_zeta(4, 2, 1);
            let ax_3 = s.get_with_zeta(3, 2, 0);
            let ax_2 = s.get_with_zeta(2, 2, 1);
            c[2][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_1 = s.get_with_zeta(1, 2, 0);
            let ax_0 = s.get_with_zeta(0, 2, 0);
            let ax_4 = s.get_with_zeta(4, 2, 0);
            let ax_3 = s.get_with_zeta(3, 2, 1);
            let ax_2 = s.get_with_zeta(2, 2, 0);
            c[2][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_4 = s.get_with_zeta(4, 3, 1);
            let ax_3 = s.get_with_zeta(3, 3, 1);
            let ax_2 = s.get_with_zeta(2, 3, 0);
            let ax_1 = s.get_with_zeta(1, 3, 1);
            let ax_0 = s.get_with_zeta(0, 3, 1);
            c[3][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_4 = s.get_with_zeta(4, 3, 0);
            let ax_3 = s.get_with_zeta(3, 3, 0);
            let ax_2 = s.get_with_zeta(2, 3, 1);
            let ax_1 = s.get_with_zeta(1, 3, 0);
            let ax_0 = s.get_with_zeta(0, 3, 0);
            c[3][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_2 = s.get_with_zeta(2, 4, 1);
            let ax_1 = s.get_with_zeta(1, 4, 0);
            let ax_0 = s.get_with_zeta(0, 4, 1);
            let ax_4 = s.get_with_zeta(4, 4, 1);
            let ax_3 = s.get_with_zeta(3, 4, 1);
            c[4][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_2 = s.get_with_zeta(2, 4, 0);
            let ax_1 = s.get_with_zeta(1, 4, 1);
            let ax_0 = s.get_with_zeta(0, 4, 0);
            let ax_4 = s.get_with_zeta(4, 4, 0);
            let ax_3 = s.get_with_zeta(3, 4, 0);
            c[4][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let c_x4_zeta0 = c[4][0];
            let c_x1_zeta1 = c[1][1];
            let c_x3_zeta0 = c[3][0];
            let c_x0_zeta1 = c[0][1];
            let c_x2_zeta0 = c[2][0];
            let c_x4_zeta1 = c[4][1];
            let d_x0_zeta0 = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
            d[0][0] = d_x0_zeta0;
            let d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
            d[2][1] = d_x2_zeta1;
            let d_x4_zeta0 = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
            d[4][0] = d_x4_zeta0;
            let d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
            d[1][1] = d_x1_zeta1;
            let d_x3_zeta0 = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
            d[3][0] = d_x3_zeta0;
            let c_x1_zeta0 = c[1][0];
            let c_x3_zeta1 = c[3][1];
            let c_x2_zeta1 = c[2][1];
            let c_x0_zeta0 = c[0][0];
            let d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
            d[0][1] = d_x0_zeta1;
            let d_x2_zeta0 = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
            d[2][0] = d_x2_zeta0;
            let d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
            d[4][1] = d_x4_zeta1;
            let d_x1_zeta0 = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
            d[1][0] = d_x1_zeta0;
            let d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
            d[3][1] = d_x3_zeta1;
        }
        {
            let (bx0, bx1) = {
                let a0 = s.get_with_zeta(0, 0, 0);
                let d0 = d[0][0];
                let a1 = s.get_with_zeta(2, 1, 1);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
            };
            let (bx2, bx3, bx4) = {
                let a2 = s.get_with_zeta(4, 2, 0);
                let d2 = d[2][1];
                let a3 = s.get_with_zeta(1, 3, 0);
                let d3 = d[3][1];
                let a4 = s.get_with_zeta(3, 4, 1);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(22),
                    (a3 ^ d3).rotate_left(11),
                    (a4 ^ d4).rotate_left(7),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(0, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(2, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(4, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(1, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(3, 4, 1, ax4);
        }
        let az0 = s.get_with_zeta(0, 0, 0);
        s.set_with_zeta(0, 0, 0, az0 ^ RC_INTERLEAVED_0[i + 2]);
        {
            let (bx0, bx1) = {
                let a0 = s.get_with_zeta(0, 0, 1);
                let d0 = d[0][1];
                let a1 = s.get_with_zeta(2, 1, 0);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
            };
            let (bx2, bx3, bx4) = {
                let a2 = s.get_with_zeta(4, 2, 1);
                let d2 = d[2][0];
                let a3 = s.get_with_zeta(1, 3, 1);
                let d3 = d[3][0];
                let a4 = s.get_with_zeta(3, 4, 0);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(21),
                    (a3 ^ d3).rotate_left(10),
                    (a4 ^ d4).rotate_left(7),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(0, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(2, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(4, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(1, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(3, 4, 0, ax4);
        }
        let az1 = s.get_with_zeta(0, 0, 1);
        s.set_with_zeta(0, 0, 1, az1 ^ RC_INTERLEAVED_1[i + 2]);

        {
            let (bx2, bx3) = {
                let a0 = s.get_with_zeta(3, 0, 0);
                let d0 = d[0][1];
                let a1 = s.get_with_zeta(0, 1, 0);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(2), (a1 ^ d1).rotate_left(23))
            };
            let (bx4, bx0, bx1) = {
                let a2 = s.get_with_zeta(2, 2, 0);
                let d2 = d[2][1];
                let a3 = s.get_with_zeta(4, 3, 1);
                let d3 = d[3][0];
                let a4 = s.get_with_zeta(1, 4, 0);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(31),
                    (a3 ^ d3).rotate_left(14),
                    (a4 ^ d4).rotate_left(10),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(3, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(0, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(2, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(4, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(1, 4, 0, ax4);
        }
        {
            let (bx2, bx3) = {
                let a0 = s.get_with_zeta(3, 0, 1);
                let d0 = d[0][0];
                let a1 = s.get_with_zeta(0, 1, 1);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(1), (a1 ^ d1).rotate_left(22))
            };
            let (bx4, bx0, bx1) = {
                let a2 = s.get_with_zeta(2, 2, 1);
                let d2 = d[2][0];
                let a3 = s.get_with_zeta(4, 3, 0);
                let d3 = d[3][1];
                let a4 = s.get_with_zeta(1, 4, 1);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(30),
                    (a3 ^ d3).rotate_left(14),
                    (a4 ^ d4).rotate_left(10),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(3, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(0, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(2, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(4, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(1, 4, 1, ax4);
        }
        {
            let (bx4, bx0) = {
                let a0 = s.get_with_zeta(1, 0, 1);
                let d0 = d[0][0];
                let a1 = s.get_with_zeta(3, 1, 0);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(1))
            };
            let (bx1, bx2, bx3) = {
                let a2 = s.get_with_zeta(0, 2, 1);
                let d2 = d[2][0];
                let a3 = s.get_with_zeta(2, 3, 1);
                let d3 = d[3][1];
                let a4 = s.get_with_zeta(4, 4, 1);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(3),
                    (a3 ^ d3).rotate_left(13),
                    (a4 ^ d4).rotate_left(4),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(1, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(3, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(0, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(2, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(4, 4, 1, ax4);
        }
        {
            let (bx4, bx0) = {
                let a0 = s.get_with_zeta(1, 0, 0);
                let d0 = d[0][1];
                let a1 = s.get_with_zeta(3, 1, 1);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(0))
            };
            let (bx1, bx2, bx3) = {
                let a2 = s.get_with_zeta(0, 2, 0);
                let d2 = d[2][1];
                let a3 = s.get_with_zeta(2, 3, 0);
                let d3 = d[3][0];
                let a4 = s.get_with_zeta(4, 4, 0);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(3),
                    (a3 ^ d3).rotate_left(12),
                    (a4 ^ d4).rotate_left(4),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(1, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(3, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(0, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(2, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(4, 4, 0, ax4);
        }
        {
            let (bx1, bx2) = {
                let a0 = s.get_with_zeta(4, 0, 1);
                let d0 = d[0][0];
                let a1 = s.get_with_zeta(1, 1, 1);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
            };
            let (bx3, bx4, bx0) = {
                let a2 = s.get_with_zeta(3, 2, 1);
                let d2 = d[2][1];
                let a3 = s.get_with_zeta(0, 3, 1);
                let d3 = d[3][0];
                let a4 = s.get_with_zeta(2, 4, 0);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(8),
                    (a3 ^ d3).rotate_left(28),
                    (a4 ^ d4).rotate_left(14),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(4, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(1, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(3, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(0, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(2, 4, 0, ax4);
        }
        {
            let (bx1, bx2) = {
                let a0 = s.get_with_zeta(4, 0, 0);
                let d0 = d[0][1];
                let a1 = s.get_with_zeta(1, 1, 0);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
            };
            let (bx3, bx4, bx0) = {
                let a2 = s.get_with_zeta(3, 2, 0);
                let d2 = d[2][0];
                let a3 = s.get_with_zeta(0, 3, 0);
                let d3 = d[3][1];
                let a4 = s.get_with_zeta(2, 4, 1);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(7),
                    (a3 ^ d3).rotate_left(28),
                    (a4 ^ d4).rotate_left(13),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(4, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(1, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(3, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(0, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(2, 4, 1, ax4);
        }
        {
            let (bx3, bx4) = {
                let a0 = s.get_with_zeta(2, 0, 0);
                let d0 = d[0][1];
                let a1 = s.get_with_zeta(4, 1, 0);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(21), (a1 ^ d1).rotate_left(1))
            };
            let (bx0, bx1, bx2) = {
                let a2 = s.get_with_zeta(1, 2, 1);
                let d2 = d[2][0];
                let a3 = s.get_with_zeta(3, 3, 0);
                let d3 = d[3][1];
                let a4 = s.get_with_zeta(0, 4, 0);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(31),
                    (a3 ^ d3).rotate_left(28),
                    (a4 ^ d4).rotate_left(20),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(2, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(4, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(1, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(3, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(0, 4, 0, ax4);
        }
        {
            let (bx3, bx4) = {
                let a0 = s.get_with_zeta(2, 0, 1);
                let d0 = d[0][0];
                let a1 = s.get_with_zeta(4, 1, 1);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(20), (a1 ^ d1).rotate_left(1))
            };
            let (bx0, bx1, bx2) = {
                let a2 = s.get_with_zeta(1, 2, 0);
                let d2 = d[2][1];
                let a3 = s.get_with_zeta(3, 3, 1);
                let d3 = d[3][0];
                let a4 = s.get_with_zeta(0, 4, 1);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(31),
                    (a3 ^ d3).rotate_left(27),
                    (a4 ^ d4).rotate_left(19),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(2, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(4, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(1, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(3, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(0, 4, 1, ax4);
        }
    }

    fn keccak_round3(&mut self, c: &mut [[u32; 2]; 5], d: &mut [[u32; 2]; 5], i: usize) {
        let s = self;

        {
            let ax_0 = s.get_with_zeta(0, 0, 0);
            let ax_3 = s.get_with_zeta(3, 0, 0);
            let ax_1 = s.get_with_zeta(1, 0, 1);
            let ax_4 = s.get_with_zeta(4, 0, 1);
            let ax_2 = s.get_with_zeta(2, 0, 0);
            c[0][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_0 = s.get_with_zeta(0, 0, 1);
            let ax_3 = s.get_with_zeta(3, 0, 1);
            let ax_1 = s.get_with_zeta(1, 0, 0);
            let ax_4 = s.get_with_zeta(4, 0, 0);
            let ax_2 = s.get_with_zeta(2, 0, 1);
            c[0][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_2 = s.get_with_zeta(2, 1, 1);
            let ax_0 = s.get_with_zeta(0, 1, 0);
            let ax_3 = s.get_with_zeta(3, 1, 0);
            let ax_1 = s.get_with_zeta(1, 1, 1);
            let ax_4 = s.get_with_zeta(4, 1, 0);
            c[1][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_2 = s.get_with_zeta(2, 1, 0);
            let ax_0 = s.get_with_zeta(0, 1, 1);
            let ax_3 = s.get_with_zeta(3, 1, 1);
            let ax_1 = s.get_with_zeta(1, 1, 0);
            let ax_4 = s.get_with_zeta(4, 1, 1);
            c[1][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_4 = s.get_with_zeta(4, 2, 0);
            let ax_2 = s.get_with_zeta(2, 2, 0);
            let ax_0 = s.get_with_zeta(0, 2, 1);
            let ax_3 = s.get_with_zeta(3, 2, 1);
            let ax_1 = s.get_with_zeta(1, 2, 1);
            c[2][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_4 = s.get_with_zeta(4, 2, 1);
            let ax_2 = s.get_with_zeta(2, 2, 1);
            let ax_0 = s.get_with_zeta(0, 2, 0);
            let ax_3 = s.get_with_zeta(3, 2, 0);
            let ax_1 = s.get_with_zeta(1, 2, 0);
            c[2][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_1 = s.get_with_zeta(1, 3, 0);
            let ax_4 = s.get_with_zeta(4, 3, 1);
            let ax_2 = s.get_with_zeta(2, 3, 1);
            let ax_0 = s.get_with_zeta(0, 3, 1);
            let ax_3 = s.get_with_zeta(3, 3, 0);
            c[3][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_1 = s.get_with_zeta(1, 3, 1);
            let ax_4 = s.get_with_zeta(4, 3, 0);
            let ax_2 = s.get_with_zeta(2, 3, 0);
            let ax_0 = s.get_with_zeta(0, 3, 0);
            let ax_3 = s.get_with_zeta(3, 3, 1);
            c[3][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_3 = s.get_with_zeta(3, 4, 1);
            let ax_1 = s.get_with_zeta(1, 4, 0);
            let ax_4 = s.get_with_zeta(4, 4, 1);
            let ax_2 = s.get_with_zeta(2, 4, 0);
            let ax_0 = s.get_with_zeta(0, 4, 0);
            c[4][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let ax_3 = s.get_with_zeta(3, 4, 0);
            let ax_1 = s.get_with_zeta(1, 4, 1);
            let ax_4 = s.get_with_zeta(4, 4, 0);
            let ax_2 = s.get_with_zeta(2, 4, 1);
            let ax_0 = s.get_with_zeta(0, 4, 1);
            c[4][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
        }
        {
            let c_x4_zeta0 = c[4][0];
            let c_x1_zeta1 = c[1][1];
            let c_x3_zeta0 = c[3][0];
            let c_x0_zeta1 = c[0][1];
            let c_x2_zeta0 = c[2][0];
            let c_x4_zeta1 = c[4][1];
            let d_x0_zeta0 = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
            d[0][0] = d_x0_zeta0;
            let d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
            d[2][1] = d_x2_zeta1;
            let d_x4_zeta0 = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
            d[4][0] = d_x4_zeta0;
            let d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
            d[1][1] = d_x1_zeta1;
            let d_x3_zeta0 = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
            d[3][0] = d_x3_zeta0;
            let c_x1_zeta0 = c[1][0];
            let c_x3_zeta1 = c[3][1];
            let c_x2_zeta1 = c[2][1];
            let c_x0_zeta0 = c[0][0];
            let d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
            d[0][1] = d_x0_zeta1;
            let d_x2_zeta0 = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
            d[2][0] = d_x2_zeta0;
            let d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
            d[4][1] = d_x4_zeta1;
            let d_x1_zeta0 = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
            d[1][0] = d_x1_zeta0;
            let d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
            d[3][1] = d_x3_zeta1;
        }
        {
            let (bx0, bx1) = {
                let a0 = s.get_with_zeta(0, 0, 0);
                let d0 = d[0][0];
                let a1 = s.get_with_zeta(0, 1, 0);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
            };
            let (bx2, bx3, bx4) = {
                let a2 = s.get_with_zeta(0, 2, 0);
                let d2 = d[2][1];
                let a3 = s.get_with_zeta(0, 3, 0);
                let d3 = d[3][1];
                let a4 = s.get_with_zeta(0, 4, 0);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(22),
                    (a3 ^ d3).rotate_left(11),
                    (a4 ^ d4).rotate_left(7),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(0, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(0, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(0, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(0, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(0, 4, 0, ax4);
        }
        {
            let (bx0, bx1) = {
                let a0 = s.get_with_zeta(0, 0, 1);
                let d0 = d[0][1];
                let a1 = s.get_with_zeta(0, 1, 1);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
            };
            let (bx2, bx3, bx4) = {
                let a2 = s.get_with_zeta(0, 2, 1);
                let d2 = d[2][0];
                let a3 = s.get_with_zeta(0, 3, 1);
                let d3 = d[3][0];
                let a4 = s.get_with_zeta(0, 4, 1);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(21),
                    (a3 ^ d3).rotate_left(10),
                    (a4 ^ d4).rotate_left(7),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(0, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(0, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(0, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(0, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(0, 4, 1, ax4);
        }
        {
            let (bx2, bx3) = {
                let a0 = s.get_with_zeta(1, 0, 0);
                let d0 = d[0][1];
                let a1 = s.get_with_zeta(1, 1, 0);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(2), (a1 ^ d1).rotate_left(23))
            };
            let (bx4, bx0, bx1) = {
                let a2 = s.get_with_zeta(1, 2, 0);
                let d2 = d[2][1];
                let a3 = s.get_with_zeta(1, 3, 0);
                let d3 = d[3][0];
                let a4 = s.get_with_zeta(1, 4, 0);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(31),
                    (a3 ^ d3).rotate_left(14),
                    (a4 ^ d4).rotate_left(10),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(1, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(1, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(1, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(1, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(1, 4, 0, ax4);
        }
        {
            let (bx2, bx3) = {
                let a0 = s.get_with_zeta(1, 0, 1);
                let d0 = d[0][0];
                let a1 = s.get_with_zeta(1, 1, 1);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(1), (a1 ^ d1).rotate_left(22))
            };
            let (bx4, bx0, bx1) = {
                let a2 = s.get_with_zeta(1, 2, 1);
                let d2 = d[2][0];
                let a3 = s.get_with_zeta(1, 3, 1);
                let d3 = d[3][1];
                let a4 = s.get_with_zeta(1, 4, 1);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(30),
                    (a3 ^ d3).rotate_left(14),
                    (a4 ^ d4).rotate_left(10),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(1, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(1, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(1, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(1, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(1, 4, 1, ax4);
        }
        {
            let (bx4, bx0) = {
                let a0 = s.get_with_zeta(2, 0, 0);
                let d0 = d[0][0];
                let a1 = s.get_with_zeta(2, 1, 0);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(1))
            };
            let (bx1, bx2, bx3) = {
                let a2 = s.get_with_zeta(2, 2, 0);
                let d2 = d[2][0];
                let a3 = s.get_with_zeta(2, 3, 0);
                let d3 = d[3][1];
                let a4 = s.get_with_zeta(2, 4, 0);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(3),
                    (a3 ^ d3).rotate_left(13),
                    (a4 ^ d4).rotate_left(4),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(2, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(2, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(2, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(2, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(2, 4, 0, ax4);
        }
        {
            let (bx4, bx0) = {
                let a0 = s.get_with_zeta(2, 0, 1);
                let d0 = d[0][1];
                let a1 = s.get_with_zeta(2, 1, 1);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(0))
            };
            let (bx1, bx2, bx3) = {
                let a2 = s.get_with_zeta(2, 2, 1);
                let d2 = d[2][1];
                let a3 = s.get_with_zeta(2, 3, 1);
                let d3 = d[3][0];
                let a4 = s.get_with_zeta(2, 4, 1);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(3),
                    (a3 ^ d3).rotate_left(12),
                    (a4 ^ d4).rotate_left(4),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(2, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(2, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(2, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(2, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(2, 4, 1, ax4);
        }
        {
            let (bx1, bx2) = {
                let a0 = s.get_with_zeta(3, 0, 0);
                let d0 = d[0][0];
                let a1 = s.get_with_zeta(3, 1, 0);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
            };
            let (bx3, bx4, bx0) = {
                let a2 = s.get_with_zeta(3, 2, 0);
                let d2 = d[2][1];
                let a3 = s.get_with_zeta(3, 3, 0);
                let d3 = d[3][0];
                let a4 = s.get_with_zeta(3, 4, 0);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(8),
                    (a3 ^ d3).rotate_left(28),
                    (a4 ^ d4).rotate_left(14),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(3, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(3, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(3, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(3, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(3, 4, 0, ax4);
        }
        {
            let (bx1, bx2) = {
                let a0 = s.get_with_zeta(3, 0, 1);
                let d0 = d[0][1];
                let a1 = s.get_with_zeta(3, 1, 1);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
            };
            let (bx3, bx4, bx0) = {
                let a2 = s.get_with_zeta(3, 2, 1);
                let d2 = d[2][0];
                let a3 = s.get_with_zeta(3, 3, 1);
                let d3 = d[3][1];
                let a4 = s.get_with_zeta(3, 4, 1);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(7),
                    (a3 ^ d3).rotate_left(28),
                    (a4 ^ d4).rotate_left(13),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(3, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(3, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(3, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(3, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(3, 4, 1, ax4);
        }
        {
            let (bx3, bx4) = {
                let a0 = s.get_with_zeta(4, 0, 0);
                let d0 = d[0][1];
                let a1 = s.get_with_zeta(4, 1, 0);
                let d1 = d[1][0];
                ((a0 ^ d0).rotate_left(21), (a1 ^ d1).rotate_left(1))
            };
            let (bx0, bx1, bx2) = {
                let a2 = s.get_with_zeta(4, 2, 0);
                let d2 = d[2][0];
                let a3 = s.get_with_zeta(4, 3, 0);
                let d3 = d[3][1];
                let a4 = s.get_with_zeta(4, 4, 0);
                let d4 = d[4][1];
                (
                    (a2 ^ d2).rotate_left(31),
                    (a3 ^ d3).rotate_left(28),
                    (a4 ^ d4).rotate_left(20),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(4, 0, 0, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(4, 1, 0, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(4, 2, 0, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(4, 3, 0, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(4, 4, 0, ax4);
        }
        {
            let (bx3, bx4) = {
                let a0 = s.get_with_zeta(4, 0, 1);
                let d0 = d[0][0];
                let a1 = s.get_with_zeta(4, 1, 1);
                let d1 = d[1][1];
                ((a0 ^ d0).rotate_left(20), (a1 ^ d1).rotate_left(1))
            };
            let (bx0, bx1, bx2) = {
                let a2 = s.get_with_zeta(4, 2, 1);
                let d2 = d[2][1];
                let a3 = s.get_with_zeta(4, 3, 1);
                let d3 = d[3][0];
                let a4 = s.get_with_zeta(4, 4, 1);
                let d4 = d[4][0];
                (
                    (a2 ^ d2).rotate_left(31),
                    (a3 ^ d3).rotate_left(27),
                    (a4 ^ d4).rotate_left(19),
                )
            };
            let ax0 = bx0 ^ ((!bx1) & bx2);
            s.set_with_zeta(4, 0, 1, ax0);
            let ax1 = bx1 ^ ((!bx2) & bx3);
            s.set_with_zeta(4, 1, 1, ax1);
            let ax2 = bx2 ^ ((!bx3) & bx4);
            s.set_with_zeta(4, 2, 1, ax2);
            let ax3 = bx3 ^ ((!bx4) & bx0);
            s.set_with_zeta(4, 3, 1, ax3);
            let ax4 = bx4 ^ ((!bx0) & bx1);
            s.set_with_zeta(4, 4, 1, ax4);
        }
        let az0 = s.get_with_zeta(0, 0, 0);
        let az1 = s.get_with_zeta(0, 0, 1);
        s.set_with_zeta(0, 0, 0, az0 ^ RC_INTERLEAVED_0[i + 3]);
        s.set_with_zeta(0, 0, 1, az1 ^ RC_INTERLEAVED_1[i + 3]);
    }
}

const RC_INTERLEAVED_0: [u32; 255] = [
    0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000001,
    0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000001,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000000,
    0x00000000, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000001,
    0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000001,
    0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000001,
    0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000001,
    0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000000,
    0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000001,
    0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000000,
    0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000000,
    0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000000,
    0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000001,
    0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000000,
    0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001,
    0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000001,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000001, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000001,
    0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000001,
    0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000001,
    0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000001,
    0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000001,
    0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000001,
    0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000001,
    0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000000,
];

const RC_INTERLEAVED_1: [u32; 255] = [
    0x00000000, 0x00000089, 0x8000008b, 0x80008080, 0x0000008b, 0x00008000, 0x80008088, 0x80000082,
    0x0000000b, 0x0000000a, 0x00008082, 0x00008003, 0x0000808b, 0x8000000b, 0x8000008a, 0x80000081,
    0x80000081, 0x80000008, 0x00000083, 0x80008003, 0x80008088, 0x80000088, 0x00008000, 0x80008082,
    0x80008089, 0x80008083, 0x80000001, 0x80008002, 0x80000089, 0x00000082, 0x80000008, 0x00000089,
    0x80000008, 0x00000000, 0x00000083, 0x80008080, 0x00000008, 0x80000080, 0x80008080, 0x00000002,
    0x8000808b, 0x00000008, 0x80000009, 0x0000800b, 0x80008082, 0x80008000, 0x00008008, 0x00008081,
    0x80008089, 0x80008089, 0x8000800a, 0x0000008a, 0x00000082, 0x80000002, 0x00008082, 0x00008080,
    0x8000000b, 0x80000003, 0x0000000a, 0x00008001, 0x80000083, 0x00008083, 0x0000008b, 0x0000800a,
    0x80000083, 0x0000800a, 0x80000000, 0x8000008a, 0x80000008, 0x0000000a, 0x00008088, 0x00000008,
    0x80000003, 0x00000000, 0x0000000a, 0x0000800b, 0x80008088, 0x8000000b, 0x80000080, 0x8000808a,
    0x00008009, 0x00000003, 0x80000003, 0x00000089, 0x80000081, 0x8000008b, 0x80008003, 0x8000800b,
    0x00008008, 0x00008008, 0x00008002, 0x00000009, 0x80008081, 0x0000808a, 0x8000800a, 0x00000080,
    0x00008089, 0x0000808a, 0x80008089, 0x80008000, 0x00008081, 0x8000800a, 0x00000009, 0x80008002,
    0x8000000a, 0x80008002, 0x80000000, 0x80000009, 0x00008088, 0x00000002, 0x80008008, 0x80008088,
    0x80000001, 0x8000808b, 0x00000002, 0x80008002, 0x80000083, 0x00008089, 0x00008080, 0x80000082,
    0x00000088, 0x8000808a, 0x0000808a, 0x80008083, 0x8000000b, 0x80000009, 0x00008001, 0x80000089,
    0x00000088, 0x80008003, 0x80008001, 0x00000003, 0x80000080, 0x80008009, 0x80000089, 0x0000000b,
    0x00000083, 0x80008009, 0x80000083, 0x00008000, 0x8000800b, 0x00008002, 0x00000003, 0x8000008a,
    0x80000002, 0x00008001, 0x80000000, 0x80000003, 0x00000083, 0x8000808a, 0x00008003, 0x00008008,
    0x0000808b, 0x80000082, 0x00000001, 0x00008001, 0x8000000a, 0x80008008, 0x8000800b, 0x00008081,
    0x80008083, 0x80000082, 0x00000082, 0x80000081, 0x80000002, 0x00008088, 0x0000008b, 0x00008083,
    0x00000008, 0x8000008a, 0x8000008b, 0x8000808a, 0x00008080, 0x80000088, 0x00008083, 0x00000002,
    0x80008081, 0x00008003, 0x00008081, 0x80008000, 0x00008002, 0x0000008a, 0x00000001, 0x00008082,
    0x0000808a, 0x80008000, 0x0000808b, 0x80000001, 0x80008081, 0x00008009, 0x0000008a, 0x00000088,
    0x80008009, 0x8000000a, 0x8000808b, 0x0000008b, 0x00008089, 0x00008003, 0x00008002, 0x00000080,
    0x0000800a, 0x8000000a, 0x80008081, 0x00008080, 0x80000001, 0x80008008, 0x80008082, 0x8000800a,
    0x00000003, 0x80000009, 0x00008082, 0x00008009, 0x00000080, 0x00008083, 0x00000081, 0x00000001,
    0x0000800b, 0x80008001, 0x00000080, 0x00008000, 0x80008001, 0x00000009, 0x8000808b, 0x00000081,
    0x00000082, 0x8000008b, 0x80008009, 0x80000000, 0x80000080, 0x80008003, 0x80008082, 0x80008083,
    0x80000088, 0x00008089, 0x00008009, 0x00000009, 0x80008008, 0x80008001, 0x0000008a, 0x0000000b,
    0x00000089, 0x80000002, 0x0000800b, 0x8000800b, 0x0000808b, 0x80000088, 0x0000800a, 0x80000089,
    0x00000001, 0x00008088, 0x00000081, 0x00000088, 0x80008080, 0x00000081, 0x0000000b,
];
