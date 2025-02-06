use arithmetic::plantard_double_ct_reference;
use vector::{pack, unpack, PackedVector};

use crate::{polynomial::PolynomialRingElement, vector::portable::PortableVector};

pub mod arithmetic;
mod intrinsics;
pub mod vector;

#[rustfmt::skip]
const PLANTARD_ZETAS: [i32; 128] = 
    [1290168, -2064267850, -966335387, -51606696, -886345008, 812805467, -1847519726, 1094061961,
     1370157786, -1819136043, 249002310, 1028263423, -700560901, -89021551, 734105255, -2042335004,
     381889553, -1137927652, 1727534158, 1904287092, -365117376, 72249375, -1404992305, 1719793153,
     1839778722, -1593356746, 690239563, -576704830, -1207596692, -580575332, -1748176835, 1059227441,
     372858381, 427045412, -98052722, -2029433330, 1544330386, -1322421591, -1357256111, -1643673275,
     838608815, -1744306333, -1052776603, 815385801, -598637676, 42575525, 1703020977, -1824296712,
     -1303069080, 1851390229, 1041165097, 583155668, 1855260731, -594767174, 1979116802, -1195985185,
     -879894171, -918599193, 1910737929, 836028480, -1103093132, -282546662, 1583035408, 1174052340,
     21932846, -732815086, 752167598, -877313836, 2112004045, 932791035, -1343064270, 1419184148,
     1817845876, -860541660, -61928035, 300609006, 975366560, -1513366367, -405112565, -359956706,
     -2097812202, 2130066389, -696690399, -1986857805, -1912028096, 1228239371, 1884934581, -828287474,
     1211467195, -1317260921, -1150829326, -1214047529, 945692709, -1279846067, 345764865, 826997308,
     2043625172, -1330162596, -1666896289, -140628247, 483812778, -1006330577, -1598517416, 2122325384,
     1371447954, 411563403, -717333077, 976656727, -1586905909, 723783916, -1113414471, -948273043,
     -677337888, 1408862808, 519937465, 1323711759, 1474661346, -1521107372, -714752743, 1143088323,
     -2073299022, 1563682897, -1877193576, 1327582262, -1572714068, -508325958, 1141798155, -1515946702];

pub(crate) fn plantard_zeta(index: usize) -> i32 {
    PLANTARD_ZETAS[index]
}

pub(crate) fn ntt_at_layer(zeta_i: &mut usize, re: &mut [u32; 128], layer: usize) {
    let step = 1 << (layer - 1);

    let _zeta_i_init = *zeta_i;

    for round in 0..(128 >> layer) {
        *zeta_i += 1;
        let offset = round * step * 2;

        for j in offset..offset + step {
            let (x, y) = plantard_double_ct_reference(re[j], re[j + step], PLANTARD_ZETAS[*zeta_i]);
            re[j] = x;
            re[j + step] = y;
        }
    }
}

// We take a flat coefficient vector as input.
pub fn ntt(re: &mut [i16; 256]) {
    let mut packed: [u32; 128] = core::array::from_fn(|i| pack(re[i], re[i + 1]));

    let mut zeta_i = 0;
    for i in (1..8).rev() {
        ntt_at_layer(&mut zeta_i, &mut packed, i);
    }

    for i in 0..128 {
        let (a, b) = unpack(packed[i]);
        re[i] = a;

        re[i + 1] = b;
    }
}
