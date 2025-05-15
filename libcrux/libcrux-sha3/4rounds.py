import numpy

Aba0 = numpy.uint32(0)
Abe0 = numpy.uint32(0)
Abi0 = numpy.uint32(0)
Abo0 = numpy.uint32(0)
Abu0 = numpy.uint32(0)
Aba1 = numpy.uint32(0)
Abe1 = numpy.uint32(0)
Abi1 = numpy.uint32(0)
Abo1 = numpy.uint32(0)
Abu1 = numpy.uint32(0)
Aga0 = numpy.uint32(0)
Age0 = numpy.uint32(0)
Agi0 = numpy.uint32(0)
Ago0 = numpy.uint32(0)
Agu0 = numpy.uint32(0)
Aga1 = numpy.uint32(0)
Age1 = numpy.uint32(0)
Agi1 = numpy.uint32(0)
Ago1 = numpy.uint32(0)
Agu1 = numpy.uint32(0)
Aka0 = numpy.uint32(0)
Ake0 = numpy.uint32(0)
Aki0 = numpy.uint32(0)
Ako0 = numpy.uint32(0)
Aku0 = numpy.uint32(0)
Aka1 = numpy.uint32(0)
Ake1 = numpy.uint32(0)
Aki1 = numpy.uint32(0)
Ako1 = numpy.uint32(0)
Aku1 = numpy.uint32(0)
Ama0 = numpy.uint32(0)
Ame0 = numpy.uint32(0)
Ami0 = numpy.uint32(0)
Amo0 = numpy.uint32(0)
Amu0 = numpy.uint32(0)
Ama1 = numpy.uint32(0)
Ame1 = numpy.uint32(0)
Ami1 = numpy.uint32(0)
Amo1 = numpy.uint32(0)
Amu1 = numpy.uint32(0)
Asa0 = numpy.uint32(0)
Ase0 = numpy.uint32(0)
Asi0 = numpy.uint32(0)
Aso0 = numpy.uint32(0)
Asu0 = numpy.uint32(0)
Asa1 = numpy.uint32(0)
Ase1 = numpy.uint32(0)
Asi1 = numpy.uint32(0)
Aso1 = numpy.uint32(0)
Asu1 = numpy.uint32(0)

def ROL32(x, i):
    return numpy.left_shift(x, i) | numpy.right_shift(x, 32-i)

i = 0

RC_INTERLEAVED_0  = [
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

RC_INTERLEAVED_1 = [
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


##// --- Code for 4 rounds
##// --- using factor 2 interleaving, 64-bit lanes mapped to 32-bit words
Ca0 = Aba0^Aga0^Aka0^Ama0^Asa0
Ca1 = Aba1^Aga1^Aka1^Ama1^Asa1
Ce0 = Abe0^Age0^Ake0^Ame0^Ase0
Ce1 = Abe1^Age1^Ake1^Ame1^Ase1
Ci0 = Abi0^Agi0^Aki0^Ami0^Asi0
Ci1 = Abi1^Agi1^Aki1^Ami1^Asi1
Co0 = Abo0^Ago0^Ako0^Amo0^Aso0
Co1 = Abo1^Ago1^Ako1^Amo1^Aso1
Cu0 = Abu0^Agu0^Aku0^Amu0^Asu0
Cu1 = Abu1^Agu1^Aku1^Amu1^Asu1
Da0 = Cu0^ROL32(Ce1, 1)
Da1 = Cu1^Ce0
De0 = Ca0^ROL32(Ci1, 1)
De1 = Ca1^Ci0
Di0 = Ce0^ROL32(Co1, 1)
Di1 = Ce1^Co0
Do0 = Ci0^ROL32(Cu1, 1)
Do1 = Ci1^Cu0
Du0 = Co0^ROL32(Ca1, 1)
Du1 = Co1^Ca0

Ba = (Aba0^Da0)
Be = ROL32((Age0^De0), 22)
Bi = ROL32((Aki1^Di1), 22)
Bo = ROL32((Amo1^Do1), 11)
Bu = ROL32((Asu0^Du0), 7)
Aba0 =   Ba ^((~Be)&  Bi )
Aba0 ^= RC_INTERLEAVED_0[i+0]
Age0 =   Be ^((~Bi)&  Bo )
Aki1 =   Bi ^((~Bo)&  Bu )
Amo1 =   Bo ^((~Bu)&  Ba )
Asu0 =   Bu ^((~Ba)&  Be )

Ba = (Aba1^Da1)
Be = ROL32((Age1^De1), 22)
Bi = ROL32((Aki0^Di0), 21)
Bo = ROL32((Amo0^Do0), 10)
Bu = ROL32((Asu1^Du1), 7)
Aba1 =   Ba ^((~Be)&  Bi )
Aba1 ^= RC_INTERLEAVED_1[i+0]
Age1 =   Be ^((~Bi)&  Bo )
Aki0 =   Bi ^((~Bo)&  Bu )
Amo0 =   Bo ^((~Bu)&  Ba )
Asu1 =   Bu ^((~Ba)&  Be )

Bi = ROL32((Aka1^Da1), 2)
Bo = ROL32((Ame1^De1), 23)
Bu = ROL32((Asi1^Di1), 31)
Ba = ROL32((Abo0^Do0), 14)
Be = ROL32((Agu0^Du0), 10)
Aka1 =   Ba ^((~Be)&  Bi )
Ame1 =   Be ^((~Bi)&  Bo )
Asi1 =   Bi ^((~Bo)&  Bu )
Abo0 =   Bo ^((~Bu)&  Ba )
Agu0 =   Bu ^((~Ba)&  Be )

Bi = ROL32((Aka0^Da0), 1)
Bo = ROL32((Ame0^De0), 22)
Bu = ROL32((Asi0^Di0), 30)
Ba = ROL32((Abo1^Do1), 14)
Be = ROL32((Agu1^Du1), 10)
Aka0 =   Ba ^((~Be)&  Bi )
Ame0 =   Be ^((~Bi)&  Bo )
Asi0 =   Bi ^((~Bo)&  Bu )
Abo1 =   Bo ^((~Bu)&  Ba )
Agu1 =   Bu ^((~Ba)&  Be )

Bu = ROL32((Asa0^Da0), 9)
Ba = ROL32((Abe1^De1), 1)
Be = ROL32((Agi0^Di0), 3)
Bi = ROL32((Ako1^Do1), 13)
Bo = ROL32((Amu0^Du0), 4)
Asa0 =   Ba ^((~Be)&  Bi )
Abe1 =   Be ^((~Bi)&  Bo )
Agi0 =   Bi ^((~Bo)&  Bu )
Ako1 =   Bo ^((~Bu)&  Ba )
Amu0 =   Bu ^((~Ba)&  Be )

Bu = ROL32((Asa1^Da1), 9)
Ba = (Abe0^De0)
Be = ROL32((Agi1^Di1), 3)
Bi = ROL32((Ako0^Do0), 12)
Bo = ROL32((Amu1^Du1), 4)
Asa1 =   Ba ^((~Be)&  Bi )
Abe0 =   Be ^((~Bi)&  Bo )
Agi1 =   Bi ^((~Bo)&  Bu )
Ako0 =   Bo ^((~Bu)&  Ba )
Amu1 =   Bu ^((~Ba)&  Be )

Be = ROL32((Aga0^Da0), 18)
Bi = ROL32((Ake0^De0), 5)
Bo = ROL32((Ami1^Di1), 8)
Bu = ROL32((Aso0^Do0), 28)
Ba = ROL32((Abu1^Du1), 14)
Aga0 =   Ba ^((~Be)&  Bi )
Ake0 =   Be ^((~Bi)&  Bo )
Ami1 =   Bi ^((~Bo)&  Bu )
Aso0 =   Bo ^((~Bu)&  Ba )
Abu1 =   Bu ^((~Ba)&  Be )

Be = ROL32((Aga1^Da1), 18)
Bi = ROL32((Ake1^De1), 5)
Bo = ROL32((Ami0^Di0), 7)
Bu = ROL32((Aso1^Do1), 28)
Ba = ROL32((Abu0^Du0), 13)
Aga1 =   Ba ^((~Be)&  Bi )
Ake1 =   Be ^((~Bi)&  Bo )
Ami0 =   Bi ^((~Bo)&  Bu )
Aso1 =   Bo ^((~Bu)&  Ba )
Abu0 =   Bu ^((~Ba)&  Be )

Bo = ROL32((Ama1^Da1), 21)
Bu = ROL32((Ase0^De0), 1)
Ba = ROL32((Abi0^Di0), 31)
Be = ROL32((Ago1^Do1), 28)
Bi = ROL32((Aku1^Du1), 20)
Ama1 =   Ba ^((~Be)&  Bi )
Ase0 =   Be ^((~Bi)&  Bo )
Abi0 =   Bi ^((~Bo)&  Bu )
Ago1 =   Bo ^((~Bu)&  Ba )
Aku1 =   Bu ^((~Ba)&  Be )

Bo = ROL32((Ama0^Da0), 20)
Bu = ROL32((Ase1^De1), 1)
Ba = ROL32((Abi1^Di1), 31)
Be = ROL32((Ago0^Do0), 27)
Bi = ROL32((Aku0^Du0), 19)
Ama0 =   Ba ^((~Be)&  Bi )
Ase1 =   Be ^((~Bi)&  Bo )
Abi1 =   Bi ^((~Bo)&  Bu )
Ago0 =   Bo ^((~Bu)&  Ba )
Aku0 =   Bu ^((~Ba)&  Be )

Ca0 = Aba0^Aka1^Asa0^Aga0^Ama1
Ca1 = Aba1^Aka0^Asa1^Aga1^Ama0
Ce0 = Age0^Ame1^Abe1^Ake0^Ase0
Ce1 = Age1^Ame0^Abe0^Ake1^Ase1
Ci0 = Aki1^Asi1^Agi0^Ami1^Abi0
Ci1 = Aki0^Asi0^Agi1^Ami0^Abi1
Co0 = Amo1^Abo0^Ako1^Aso0^Ago1
Co1 = Amo0^Abo1^Ako0^Aso1^Ago0
Cu0 = Asu0^Agu0^Amu0^Abu1^Aku1
Cu1 = Asu1^Agu1^Amu1^Abu0^Aku0
Da0 = Cu0^ROL32(Ce1, 1)
Da1 = Cu1^Ce0
De0 = Ca0^ROL32(Ci1, 1)
De1 = Ca1^Ci0
Di0 = Ce0^ROL32(Co1, 1)
Di1 = Ce1^Co0
Do0 = Ci0^ROL32(Cu1, 1)
Do1 = Ci1^Cu0
Du0 = Co0^ROL32(Ca1, 1)
Du1 = Co1^Ca0

Ba = (Aba0^Da0)
Be = ROL32((Ame1^De0), 22)
Bi = ROL32((Agi1^Di1), 22)
Bo = ROL32((Aso1^Do1), 11)
Bu = ROL32((Aku1^Du0), 7)
Aba0 =   Ba ^((~Be)&  Bi )
Aba0 ^= RC_INTERLEAVED_0[i+1]
Ame1 =   Be ^((~Bi)&  Bo )
Agi1 =   Bi ^((~Bo)&  Bu )
Aso1 =   Bo ^((~Bu)&  Ba )
Aku1 =   Bu ^((~Ba)&  Be )

Ba = (Aba1^Da1)
Be = ROL32((Ame0^De1), 22)
Bi = ROL32((Agi0^Di0), 21)
Bo = ROL32((Aso0^Do0), 10)
Bu = ROL32((Aku0^Du1), 7)
Aba1 =   Ba ^((~Be)&  Bi )
Aba1 ^= RC_INTERLEAVED_1[i+1]
Ame0 =   Be ^((~Bi)&  Bo )
Agi0 =   Bi ^((~Bo)&  Bu )
Aso0 =   Bo ^((~Bu)&  Ba )
Aku0 =   Bu ^((~Ba)&  Be )

Bi = ROL32((Asa1^Da1), 2)
Bo = ROL32((Ake1^De1), 23)
Bu = ROL32((Abi1^Di1), 31)
Ba = ROL32((Amo1^Do0), 14)
Be = ROL32((Agu0^Du0), 10)
Asa1 =   Ba ^((~Be)&  Bi )
Ake1 =   Be ^((~Bi)&  Bo )
Abi1 =   Bi ^((~Bo)&  Bu )
Amo1 =   Bo ^((~Bu)&  Ba )
Agu0 =   Bu ^((~Ba)&  Be )

Bi = ROL32((Asa0^Da0), 1)
Bo = ROL32((Ake0^De0), 22)
Bu = ROL32((Abi0^Di0), 30)
Ba = ROL32((Amo0^Do1), 14)
Be = ROL32((Agu1^Du1), 10)
Asa0 =   Ba ^((~Be)&  Bi )
Ake0 =   Be ^((~Bi)&  Bo )
Abi0 =   Bi ^((~Bo)&  Bu )
Amo0 =   Bo ^((~Bu)&  Ba )
Agu1 =   Bu ^((~Ba)&  Be )

Bu = ROL32((Ama1^Da0), 9)
Ba = ROL32((Age1^De1), 1)
Be = ROL32((Asi1^Di0), 3)
Bi = ROL32((Ako0^Do1), 13)
Bo = ROL32((Abu1^Du0), 4)
Ama1 =   Ba ^((~Be)&  Bi )
Age1 =   Be ^((~Bi)&  Bo )
Asi1 =   Bi ^((~Bo)&  Bu )
Ako0 =   Bo ^((~Bu)&  Ba )
Abu1 =   Bu ^((~Ba)&  Be )

Bu = ROL32((Ama0^Da1), 9)
Ba = (Age0^De0)
Be = ROL32((Asi0^Di1), 3)
Bi = ROL32((Ako1^Do0), 12)
Bo = ROL32((Abu0^Du1), 4)
Ama0 =   Ba ^((~Be)&  Bi )
Age0 =   Be ^((~Bi)&  Bo )
Asi0 =   Bi ^((~Bo)&  Bu )
Ako1 =   Bo ^((~Bu)&  Ba )
Abu0 =   Bu ^((~Ba)&  Be )

Be = ROL32((Aka1^Da0), 18)
Bi = ROL32((Abe1^De0), 5)
Bo = ROL32((Ami0^Di1), 8)
Bu = ROL32((Ago1^Do0), 28)
Ba = ROL32((Asu1^Du1), 14)
Aka1 =   Ba ^((~Be)&  Bi )
Abe1 =   Be ^((~Bi)&  Bo )
Ami0 =   Bi ^((~Bo)&  Bu )
Ago1 =   Bo ^((~Bu)&  Ba )
Asu1 =   Bu ^((~Ba)&  Be )

Be = ROL32((Aka0^Da1), 18)
Bi = ROL32((Abe0^De1), 5)
Bo = ROL32((Ami1^Di0), 7)
Bu = ROL32((Ago0^Do1), 28)
Ba = ROL32((Asu0^Du0), 13)
Aka0 =   Ba ^((~Be)&  Bi )
Abe0 =   Be ^((~Bi)&  Bo )
Ami1 =   Bi ^((~Bo)&  Bu )
Ago0 =   Bo ^((~Bu)&  Ba )
Asu0 =   Bu ^((~Ba)&  Be )

Bo = ROL32((Aga1^Da1), 21)
Bu = ROL32((Ase0^De0), 1)
Ba = ROL32((Aki1^Di0), 31)
Be = ROL32((Abo1^Do1), 28)
Bi = ROL32((Amu1^Du1), 20)
Aga1 =   Ba ^((~Be)&  Bi )
Ase0 =   Be ^((~Bi)&  Bo )
Aki1 =   Bi ^((~Bo)&  Bu )
Abo1 =   Bo ^((~Bu)&  Ba )
Amu1 =   Bu ^((~Ba)&  Be )

Bo = ROL32((Aga0^Da0), 20)
Bu = ROL32((Ase1^De1), 1)
Ba = ROL32((Aki0^Di1), 31)
Be = ROL32((Abo0^Do0), 27)
Bi = ROL32((Amu0^Du0), 19)
Aga0 =   Ba ^((~Be)&  Bi )
Ase1 =   Be ^((~Bi)&  Bo )
Aki0 =   Bi ^((~Bo)&  Bu )
Abo0 =   Bo ^((~Bu)&  Ba )
Amu0 =   Bu ^((~Ba)&  Be )

Ca0 = Aba0^Asa1^Ama1^Aka1^Aga1
Ca1 = Aba1^Asa0^Ama0^Aka0^Aga0
Ce0 = Ame1^Ake1^Age1^Abe1^Ase0
Ce1 = Ame0^Ake0^Age0^Abe0^Ase1
Ci0 = Agi1^Abi1^Asi1^Ami0^Aki1
Ci1 = Agi0^Abi0^Asi0^Ami1^Aki0
Co0 = Aso1^Amo1^Ako0^Ago1^Abo1
Co1 = Aso0^Amo0^Ako1^Ago0^Abo0
Cu0 = Aku1^Agu0^Abu1^Asu1^Amu1
Cu1 = Aku0^Agu1^Abu0^Asu0^Amu0
Da0 = Cu0^ROL32(Ce1, 1)
Da1 = Cu1^Ce0
De0 = Ca0^ROL32(Ci1, 1)
De1 = Ca1^Ci0
Di0 = Ce0^ROL32(Co1, 1)
Di1 = Ce1^Co0
Do0 = Ci0^ROL32(Cu1, 1)
Do1 = Ci1^Cu0
Du0 = Co0^ROL32(Ca1, 1)
Du1 = Co1^Ca0

Ba = (Aba0^Da0)
Be = ROL32((Ake1^De0), 22)
Bi = ROL32((Asi0^Di1), 22)
Bo = ROL32((Ago0^Do1), 11)
Bu = ROL32((Amu1^Du0), 7)
Aba0 =   Ba ^((~Be)&  Bi )
Aba0 ^= RC_INTERLEAVED_0[i+2]
Ake1 =   Be ^((~Bi)&  Bo )
Asi0 =   Bi ^((~Bo)&  Bu )
Ago0 =   Bo ^((~Bu)&  Ba )
Amu1 =   Bu ^((~Ba)&  Be )

Ba = (Aba1^Da1)
Be = ROL32((Ake0^De1), 22)
Bi = ROL32((Asi1^Di0), 21)
Bo = ROL32((Ago1^Do0), 10)
Bu = ROL32((Amu0^Du1), 7)
Aba1 =   Ba ^((~Be)&  Bi )
Aba1 ^= RC_INTERLEAVED_1[i+2]
Ake0 =   Be ^((~Bi)&  Bo )
Asi1 =   Bi ^((~Bo)&  Bu )
Ago1 =   Bo ^((~Bu)&  Ba )
Amu0 =   Bu ^((~Ba)&  Be )

Bi = ROL32((Ama0^Da1), 2)
Bo = ROL32((Abe0^De1), 23)
Bu = ROL32((Aki0^Di1), 31)
Ba = ROL32((Aso1^Do0), 14)
Be = ROL32((Agu0^Du0), 10)
Ama0 =   Ba ^((~Be)&  Bi )
Abe0 =   Be ^((~Bi)&  Bo )
Aki0 =   Bi ^((~Bo)&  Bu )
Aso1 =   Bo ^((~Bu)&  Ba )
Agu0 =   Bu ^((~Ba)&  Be )

Bi = ROL32((Ama1^Da0), 1)
Bo = ROL32((Abe1^De0), 22)
Bu = ROL32((Aki1^Di0), 30)
Ba = ROL32((Aso0^Do1), 14)
Be = ROL32((Agu1^Du1), 10)
Ama1 =   Ba ^((~Be)&  Bi )
Abe1 =   Be ^((~Bi)&  Bo )
Aki1 =   Bi ^((~Bo)&  Bu )
Aso0 =   Bo ^((~Bu)&  Ba )
Agu1 =   Bu ^((~Ba)&  Be )

Bu = ROL32((Aga1^Da0), 9)
Ba = ROL32((Ame0^De1), 1)
Be = ROL32((Abi1^Di0), 3)
Bi = ROL32((Ako1^Do1), 13)
Bo = ROL32((Asu1^Du0), 4)
Aga1 =   Ba ^((~Be)&  Bi )
Ame0 =   Be ^((~Bi)&  Bo )
Abi1 =   Bi ^((~Bo)&  Bu )
Ako1 =   Bo ^((~Bu)&  Ba )
Asu1 =   Bu ^((~Ba)&  Be )

Bu = ROL32((Aga0^Da1), 9)
Ba = (Ame1^De0)
Be = ROL32((Abi0^Di1), 3)
Bi = ROL32((Ako0^Do0), 12)
Bo = ROL32((Asu0^Du1), 4)
Aga0 =   Ba ^((~Be)&  Bi )
Ame1 =   Be ^((~Bi)&  Bo )
Abi0 =   Bi ^((~Bo)&  Bu )
Ako0 =   Bo ^((~Bu)&  Ba )
Asu0 =   Bu ^((~Ba)&  Be )

Be = ROL32((Asa1^Da0), 18)
Bi = ROL32((Age1^De0), 5)
Bo = ROL32((Ami1^Di1), 8)
Bu = ROL32((Abo1^Do0), 28)
Ba = ROL32((Aku0^Du1), 14)
Asa1 =   Ba ^((~Be)&  Bi )
Age1 =   Be ^((~Bi)&  Bo )
Ami1 =   Bi ^((~Bo)&  Bu )
Abo1 =   Bo ^((~Bu)&  Ba )
Aku0 =   Bu ^((~Ba)&  Be )

Be = ROL32((Asa0^Da1), 18)
Bi = ROL32((Age0^De1), 5)
Bo = ROL32((Ami0^Di0), 7)
Bu = ROL32((Abo0^Do1), 28)
Ba = ROL32((Aku1^Du0), 13)
Asa0 =   Ba ^((~Be)&  Bi )
Age0 =   Be ^((~Bi)&  Bo )
Ami0 =   Bi ^((~Bo)&  Bu )
Abo0 =   Bo ^((~Bu)&  Ba )
Aku1 =   Bu ^((~Ba)&  Be )

Bo = ROL32((Aka0^Da1), 21)
Bu = ROL32((Ase0^De0), 1)
Ba = ROL32((Agi1^Di0), 31)
Be = ROL32((Amo0^Do1), 28)
Bi = ROL32((Abu0^Du1), 20)
Aka0 =   Ba ^((~Be)&  Bi )
Ase0 =   Be ^((~Bi)&  Bo )
Agi1 =   Bi ^((~Bo)&  Bu )
Amo0 =   Bo ^((~Bu)&  Ba )
Abu0 =   Bu ^((~Ba)&  Be )

Bo = ROL32((Aka1^Da0), 20)
Bu = ROL32((Ase1^De1), 1)
Ba = ROL32((Agi0^Di1), 31)
Be = ROL32((Amo1^Do0), 27)
Bi = ROL32((Abu1^Du0), 19)
Aka1 =   Ba ^((~Be)&  Bi )
Ase1 =   Be ^((~Bi)&  Bo )
Agi0 =   Bi ^((~Bo)&  Bu )
Amo1 =   Bo ^((~Bu)&  Ba )
Abu1 =   Bu ^((~Ba)&  Be )

Ca0 = Aba0^Ama0^Aga1^Asa1^Aka0
Ca1 = Aba1^Ama1^Aga0^Asa0^Aka1
Ce0 = Ake1^Abe0^Ame0^Age1^Ase0
Ce1 = Ake0^Abe1^Ame1^Age0^Ase1
Ci0 = Asi0^Aki0^Abi1^Ami1^Agi1
Ci1 = Asi1^Aki1^Abi0^Ami0^Agi0
Co0 = Ago0^Aso1^Ako1^Abo1^Amo0
Co1 = Ago1^Aso0^Ako0^Abo0^Amo1
Cu0 = Amu1^Agu0^Asu1^Aku0^Abu0
Cu1 = Amu0^Agu1^Asu0^Aku1^Abu1
Da0 = Cu0^ROL32(Ce1, 1)
Da1 = Cu1^Ce0
De0 = Ca0^ROL32(Ci1, 1)
De1 = Ca1^Ci0
Di0 = Ce0^ROL32(Co1, 1)
Di1 = Ce1^Co0
Do0 = Ci0^ROL32(Cu1, 1)
Do1 = Ci1^Cu0
Du0 = Co0^ROL32(Ca1, 1)
Du1 = Co1^Ca0

Ba = (Aba0^Da0)
Be = ROL32((Abe0^De0), 22)
Bi = ROL32((Abi0^Di1), 22)
Bo = ROL32((Abo0^Do1), 11)
Bu = ROL32((Abu0^Du0), 7)
Aba0 =   Ba ^((~Be)&  Bi )
Aba0 ^= RC_INTERLEAVED_0[i+3]
Abe0 =   Be ^((~Bi)&  Bo )
Abi0 =   Bi ^((~Bo)&  Bu )
Abo0 =   Bo ^((~Bu)&  Ba )
Abu0 =   Bu ^((~Ba)&  Be )

Ba = (Aba1^Da1)
Be = ROL32((Abe1^De1), 22)
Bi = ROL32((Abi1^Di0), 21)
Bo = ROL32((Abo1^Do0), 10)
Bu = ROL32((Abu1^Du1), 7)
Aba1 =   Ba ^((~Be)&  Bi )
Aba1 ^= RC_INTERLEAVED_1[i+3]
Abe1 =   Be ^((~Bi)&  Bo )
Abi1 =   Bi ^((~Bo)&  Bu )
Abo1 =   Bo ^((~Bu)&  Ba )
Abu1 =   Bu ^((~Ba)&  Be )

Bi = ROL32((Aga0^Da1), 2)
Bo = ROL32((Age0^De1), 23)
Bu = ROL32((Agi0^Di1), 31)
Ba = ROL32((Ago0^Do0), 14)
Be = ROL32((Agu0^Du0), 10)
Aga0 =   Ba ^((~Be)&  Bi )
Age0 =   Be ^((~Bi)&  Bo )
Agi0 =   Bi ^((~Bo)&  Bu )
Ago0 =   Bo ^((~Bu)&  Ba )
Agu0 =   Bu ^((~Ba)&  Be )

Bi = ROL32((Aga1^Da0), 1)
Bo = ROL32((Age1^De0), 22)
Bu = ROL32((Agi1^Di0), 30)
Ba = ROL32((Ago1^Do1), 14)
Be = ROL32((Agu1^Du1), 10)
Aga1 =   Ba ^((~Be)&  Bi )
Age1 =   Be ^((~Bi)&  Bo )
Agi1 =   Bi ^((~Bo)&  Bu )
Ago1 =   Bo ^((~Bu)&  Ba )
Agu1 =   Bu ^((~Ba)&  Be )

Bu = ROL32((Aka0^Da0), 9)
Ba = ROL32((Ake0^De1), 1)
Be = ROL32((Aki0^Di0), 3)
Bi = ROL32((Ako0^Do1), 13)
Bo = ROL32((Aku0^Du0), 4)
Aka0 =   Ba ^((~Be)&  Bi )
Ake0 =   Be ^((~Bi)&  Bo )
Aki0 =   Bi ^((~Bo)&  Bu )
Ako0 =   Bo ^((~Bu)&  Ba )
Aku0 =   Bu ^((~Ba)&  Be )

Bu = ROL32((Aka1^Da1), 9)
Ba = (Ake1^De0)
Be = ROL32((Aki1^Di1), 3)
Bi = ROL32((Ako1^Do0), 12)
Bo = ROL32((Aku1^Du1), 4)
Aka1 =   Ba ^((~Be)&  Bi )
Ake1 =   Be ^((~Bi)&  Bo )
Aki1 =   Bi ^((~Bo)&  Bu )
Ako1 =   Bo ^((~Bu)&  Ba )
Aku1 =   Bu ^((~Ba)&  Be )

Be = ROL32((Ama0^Da0), 18)
Bi = ROL32((Ame0^De0), 5)
Bo = ROL32((Ami0^Di1), 8)
Bu = ROL32((Amo0^Do0), 28)
Ba = ROL32((Amu0^Du1), 14)
Ama0 =   Ba ^((~Be)&  Bi )
Ame0 =   Be ^((~Bi)&  Bo )
Ami0 =   Bi ^((~Bo)&  Bu )
Amo0 =   Bo ^((~Bu)&  Ba )
Amu0 =   Bu ^((~Ba)&  Be )

Be = ROL32((Ama1^Da1), 18)
Bi = ROL32((Ame1^De1), 5)
Bo = ROL32((Ami1^Di0), 7)
Bu = ROL32((Amo1^Do1), 28)
Ba = ROL32((Amu1^Du0), 13)
Ama1 =   Ba ^((~Be)&  Bi )
Ame1 =   Be ^((~Bi)&  Bo )
Ami1 =   Bi ^((~Bo)&  Bu )
Amo1 =   Bo ^((~Bu)&  Ba )
Amu1 =   Bu ^((~Ba)&  Be )

Bo = ROL32((Asa0^Da1), 21)
Bu = ROL32((Ase0^De0), 1)
Ba = ROL32((Asi0^Di0), 31)
Be = ROL32((Aso0^Do1), 28)
Bi = ROL32((Asu0^Du1), 20)
Asa0 =   Ba ^((~Be)&  Bi )
Ase0 =   Be ^((~Bi)&  Bo )
Asi0 =   Bi ^((~Bo)&  Bu )
Aso0 =   Bo ^((~Bu)&  Ba )
Asu0 =   Bu ^((~Ba)&  Be )

Bo = ROL32((Asa1^Da0), 20)
Bu = ROL32((Ase1^De1), 1)
Ba = ROL32((Asi1^Di1), 31)
Be = ROL32((Aso1^Do0), 27)
Bi = ROL32((Asu1^Du0), 19)
Asa1 =   Ba ^((~Be)&  Bi )
Ase1 =   Be ^((~Bi)&  Bo )
Asi1 =   Bi ^((~Bo)&  Bu )
Aso1 =   Bo ^((~Bu)&  Ba )
Asu1 =   Bu ^((~Ba)&  Be )

print(Aba0, Abe0, Abi0, Abo0, Abu0)
print(Aba1, Abe1, Abi1, Abo1, Abu1)
print(Aga0, Age0, Agi0, Ago0, Agu0)
print(Aga1, Age1, Agi1, Ago1, Agu1)
print(Aka0, Ake0, Aki0, Ako0, Aku0)
print(Aka1, Ake1, Aki1, Ako1, Aku1)
print(Ama0, Ame0, Ami0, Amo0, Amu0)
print(Ama1, Ame1, Ami1, Amo1, Amu1)
print(Asa0, Ase0, Asi0, Aso0, Asu0)
print(Asa1, Ase1, Asi1, Aso1, Asu1)
