include "c1.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "cexp.mm"
include "cuz.mm"
include "wcel.mm"
include "wss.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "crp.mm"
include "clt.mm"
include "ceu.mm"
include "csqrt.mm"
include "w3a.mm"
include "c4.mm"
include "clog.mm"
include "c2.mm"
include "c3.mm"
include "cmin.mm"
include "cdc.mm"
include "pntlemb.mm"
include "simp1d.mm"
include "cc0.mm"
include "cioo.mm"
include "pntlemc.mm"
include "simp2d.mm"
include "cfzo.mm"
include "elfzoelz.mm"
include "syl.mm"
include "peano2zd.mm"
include "rpexpcld.mm"
include "rpdivcld.mm"
include "rpred.mm"
include "flcld.mm"
include "1rp.mm"
include "pntlemd.mm"
include "rpmulcld.mm"
include "rpaddcl.mm"
include "sylancr.mm"
include "cr.mm"
include "wa.mm"
include "cv.mm"
include "cabs.mm"
include "cicc.mm"
include "wral.mm"
include "simpld.mm"
include "simprd.mm"
include "rpcnd.mm"
include "mulcomd.mm"
include "cn.mm"
include "pntlemg.mm"
include "elfzouz.mm"
include "eluznn.mm"
include "syl2anc.mm"
include "nnnn0d.mm"
include "expp1d.mm"
include "eqtr4d.mm"
include "breqtrd.mm"
include "ltled.mm"
include "lediv2d.mm"
include "mpbid.mm"
include "flwordi.mm"
include "syl3anc.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "eluzp1p1.mm"
include "fzss1.mm"
include "3syl.mm"
include "fzss2.mm"
include "sstrd.mm"
include "3sstr4g.mm"

theorem pntlemq
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cU: class U
  let cE: class E
  let cF: class F
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vx: setvar x
  let vw: setvar w
  let vn: setvar n
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vv: setvar v
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vl: setvar l
  assume pntlem1.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )
  assume pntlem1.a: |- ( ph -> A e. RR+ )
  assume pntlem1.b: |- ( ph -> B e. RR+ )
  assume pntlem1.l: |- ( ph -> L e. ( 0 (,) 1 ) )
  assume pntlem1.d: |- D = ( A + 1 )
  assume pntlem1.f: |- F = ( ( 1 - ( 1 / D ) ) x. ( ( L / ( ; 3 2 x. B ) ) / ( D ^ 2 ) ) )
  assume pntlem1.u: |- ( ph -> U e. RR+ )
  assume pntlem1.u2: |- ( ph -> U <_ A )
  assume pntlem1.e: |- E = ( U / D )
  assume pntlem1.k: |- K = ( exp ` ( B / E ) )
  assume pntlem1.y: |- ( ph -> ( Y e. RR+ /\ 1 <_ Y ) )
  assume pntlem1.x: |- ( ph -> ( X e. RR+ /\ Y < X ) )
  assume pntlem1.c: |- ( ph -> C e. RR+ )
  assume pntlem1.w: |- W = ( ( ( Y + ( 4 / ( L x. E ) ) ) ^ 2 ) + ( ( ( X x. ( K ^ 2 ) ) ^ 4 ) + ( exp ` ( ( ( ; 3 2 x. B ) / ( ( U - E ) x. ( L x. ( E ^ 2 ) ) ) ) x. ( ( U x. 3 ) + C ) ) ) ) )
  assume pntlem1.z: |- ( ph -> Z e. ( W [,) +oo ) )
  assume pntlem1.m: |- M = ( ( |_ ` ( ( log ` X ) / ( log ` K ) ) ) + 1 )
  assume pntlem1.n: |- N = ( |_ ` ( ( ( log ` Z ) / ( log ` K ) ) / 2 ) )
  assume pntlem1.U: |- ( ph -> A. z e. ( Y [,) +oo ) ( abs ` ( ( R ` z ) / z ) ) <_ U )
  assume pntlem1.K: |- ( ph -> A. y e. ( X (,) +oo ) E. z e. RR+ ( ( y < z /\ ( ( 1 + ( L x. E ) ) x. z ) < ( K x. y ) ) /\ A. u e. ( z [,] ( ( 1 + ( L x. E ) ) x. z ) ) ( abs ` ( ( R ` u ) / u ) ) <_ E ) )
  assume pntlem1.o: |- O = ( ( ( |_ ` ( Z / ( K ^ ( J + 1 ) ) ) ) + 1 ) ... ( |_ ` ( Z / ( K ^ J ) ) ) )
  assume pntlem1.v: |- ( ph -> V e. RR+ )
  assume pntlem1.V: |- ( ph -> ( ( ( K ^ J ) < V /\ ( ( 1 + ( L x. E ) ) x. V ) < ( K x. ( K ^ J ) ) ) /\ A. u e. ( V [,] ( ( 1 + ( L x. E ) ) x. V ) ) ( abs ` ( ( R ` u ) / u ) ) <_ E ) )
  assume pntlem1.j: |- ( ph -> J e. ( M ..^ N ) )
  assume pntlem1.i: |- I = ( ( ( |_ ` ( Z / ( ( 1 + ( L x. E ) ) x. V ) ) ) + 1 ) ... ( |_ ` ( Z / V ) ) )

  disjoint C z
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint u y
  disjoint u z
  disjoint L u
  disjoint L y
  disjoint L z
  disjoint K y
  disjoint K z
  disjoint M z
  disjoint O z
  disjoint N z
  disjoint R u
  disjoint R y
  disjoint R z
  disjoint V u
  disjoint U z
  disjoint W z
  disjoint X y
  disjoint X z
  disjoint Y z
  disjoint a u
  disjoint a y
  disjoint a z
  disjoint E a
  disjoint E u
  disjoint E y
  disjoint E z
  disjoint Z u
  disjoint Z z
  disjoint x z
  disjoint C x
  disjoint F w
  disjoint I n
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint J n
  disjoint x y
  disjoint J x
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j u
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint L j
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint L k
  disjoint m n
  disjoint m u
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint L m
  disjoint n u
  disjoint L n
  disjoint u x
  disjoint L x
  disjoint K j
  disjoint K k
  disjoint K m
  disjoint K n
  disjoint K x
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint O n
  disjoint O x
  disjoint j v
  disjoint j ph
  disjoint m v
  disjoint m ph
  disjoint n v
  disjoint n ph
  disjoint v x
  disjoint ph v
  disjoint ph x
  disjoint N j
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint b l
  disjoint b m
  disjoint b n
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint R b
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c i
  disjoint c j
  disjoint c k
  disjoint c l
  disjoint c m
  disjoint c n
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint R c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d l
  disjoint d m
  disjoint d n
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint R d
  disjoint e f
  disjoint e g
  disjoint e i
  disjoint e j
  disjoint e k
  disjoint e l
  disjoint e m
  disjoint e n
  disjoint e u
  disjoint e v
  disjoint e w
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint R e
  disjoint f g
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f l
  disjoint f m
  disjoint f n
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint R f
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g l
  disjoint g m
  disjoint g n
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint R g
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i n
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint R i
  disjoint j l
  disjoint j w
  disjoint R j
  disjoint k l
  disjoint k v
  disjoint k w
  disjoint R k
  disjoint l m
  disjoint l n
  disjoint l u
  disjoint l v
  disjoint l w
  disjoint l x
  disjoint l y
  disjoint l z
  disjoint R l
  disjoint m w
  disjoint R m
  disjoint n w
  disjoint R n
  disjoint u v
  disjoint u w
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint R v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint R w
  disjoint R x
  disjoint V n
  disjoint U j
  disjoint U m
  disjoint U n
  disjoint U w
  disjoint U x
  disjoint W n
  disjoint W v
  disjoint W w
  disjoint X k
  disjoint X n
  disjoint Y i
  disjoint Y j
  disjoint Y m
  disjoint Y n
  disjoint Y x
  disjoint a e
  disjoint a g
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a v
  disjoint a x
  disjoint E e
  disjoint E g
  disjoint E j
  disjoint E k
  disjoint E m
  disjoint E n
  disjoint E v
  disjoint E x
  disjoint Z j
  disjoint Z m
  disjoint Z n
  disjoint Z x
  assert |- ( ph -> I C_ O )

  proof
    wph
    cZ
    c1
    cL
    cE
    cmul
    co
    #
    caddc
    co
    #
    cV
    cmul
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cZ
    cV
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    cZ
    cK
    cJ
    c1
    caddc
    co
    #
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cZ
    cK
    cJ
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    cI
    cO
    wph
    @8
    @13
    @7
    cfz
    co
    #
    @17
    wph
    @4
    @12
    cuz
    cfv
    wcel
    #
    @5
    @13
    cuz
    cfv
    wcel
    @8
    @18
    wss
    wph
    @12
    cz
    wcel
    @4
    cz
    wcel
    @12
    @4
    cle
    wbr
    #
    @19
    wph
    @11
    wph
    @11
    wph
    cZ
    @10
    wph
    cZ
    crp
    wcel
    c1
    cZ
    clt
    wbr
    ceu
    cZ
    csqrt
    cfv
    #
    cle
    wbr
    @21
    cZ
    cY
    cdiv
    co
    cle
    wbr
    w3a
    c4
    @0
    cdiv
    co
    @21
    cle
    wbr
    cX
    clog
    cfv
    cK
    clog
    cfv
    #
    cdiv
    co
    c2
    caddc
    co
    cZ
    clog
    cfv
    #
    @22
    cdiv
    co
    c4
    cdiv
    co
    #
    cle
    wbr
    cU
    c3
    cmul
    co
    cC
    caddc
    co
    cU
    cE
    cmin
    co
    #
    cL
    cE
    c2
    cexp
    co
    cmul
    co
    c3
    c2
    cdc
    cB
    cmul
    co
    cdiv
    co
    cmul
    co
    @23
    cmul
    co
    cle
    wbr
    w3a
    wph
    cA
    cB
    cC
    cD
    cR
    cU
    cE
    cF
    cK
    cL
    cW
    cX
    cY
    cZ
    va
    pntlem1.r
    pntlem1.a
    pntlem1.b
    pntlem1.l
    pntlem1.d
    pntlem1.f
    pntlem1.u
    pntlem1.u2
    pntlem1.e
    pntlem1.k
    pntlem1.y
    pntlem1.x
    pntlem1.c
    pntlem1.w
    pntlem1.z
    pntlemb
    simp1d
    #
    wph
    cK
    @9
    wph
    cE
    crp
    wcel
    #
    cK
    crp
    wcel
    #
    cE
    cc0
    c1
    cioo
    co
    wcel
    c1
    cK
    clt
    wbr
    @25
    crp
    wcel
    w3a
    #
    wph
    cA
    cB
    cD
    cR
    cU
    cE
    cF
    cK
    cL
    va
    pntlem1.r
    pntlem1.a
    pntlem1.b
    pntlem1.l
    pntlem1.d
    pntlem1.f
    pntlem1.u
    pntlem1.u2
    pntlem1.e
    pntlem1.k
    pntlemc
    #
    simp2d
    #
    wph
    cJ
    wph
    cJ
    cM
    cN
    cfzo
    co
    wcel
    #
    cJ
    cz
    wcel
    pntlem1.j
    cJ
    cM
    cN
    elfzoelz
    syl
    #
    peano2zd
    rpexpcld
    #
    rpdivcld
    rpred
    #
    flcld
    wph
    @3
    wph
    @3
    wph
    cZ
    @2
    @26
    wph
    @1
    cV
    wph
    c1
    crp
    wcel
    @0
    crp
    wcel
    @1
    crp
    wcel
    1rp
    wph
    cL
    cE
    wph
    cL
    crp
    wcel
    cD
    crp
    wcel
    cF
    crp
    wcel
    wph
    cA
    cB
    cD
    cR
    cF
    cL
    va
    pntlem1.r
    pntlem1.a
    pntlem1.b
    pntlem1.l
    pntlem1.d
    pntlem1.f
    pntlemd
    simp1d
    wph
    @27
    @28
    @29
    @30
    simp1d
    rpmulcld
    c1
    @0
    rpaddcl
    sylancr
    pntlem1.v
    rpmulcld
    #
    rpdivcld
    rpred
    #
    flcld
    wph
    @11
    cr
    wcel
    @3
    cr
    wcel
    @11
    @3
    cle
    wbr
    #
    @20
    @35
    @37
    wph
    @2
    @10
    cle
    wbr
    @38
    wph
    @2
    @10
    wph
    @2
    @36
    rpred
    wph
    @10
    @34
    rpred
    wph
    @2
    cK
    @14
    cmul
    co
    #
    @10
    clt
    wph
    @14
    cV
    clt
    wbr
    #
    @2
    @39
    clt
    wbr
    #
    wph
    @40
    @41
    wa
    vu
    cv
    #
    cR
    cfv
    @42
    cdiv
    co
    cabs
    cfv
    cE
    cle
    wbr
    vu
    cV
    @2
    cicc
    co
    wral
    pntlem1.V
    simpld
    #
    simprd
    wph
    @39
    @14
    cK
    cmul
    co
    @10
    wph
    cK
    @14
    wph
    cK
    @31
    rpcnd
    #
    wph
    @14
    wph
    cK
    cJ
    @31
    @33
    rpexpcld
    #
    rpcnd
    mulcomd
    wph
    cK
    cJ
    @44
    wph
    cJ
    wph
    cM
    cn
    wcel
    #
    cJ
    cM
    cuz
    cfv
    #
    wcel
    #
    cJ
    cn
    wcel
    wph
    @46
    cN
    @47
    wcel
    @24
    cN
    cM
    cmin
    co
    cle
    wbr
    wph
    cA
    cB
    cC
    cD
    cR
    cU
    cE
    cF
    cK
    cL
    cM
    cN
    cW
    cX
    cY
    cZ
    va
    pntlem1.r
    pntlem1.a
    pntlem1.b
    pntlem1.l
    pntlem1.d
    pntlem1.f
    pntlem1.u
    pntlem1.u2
    pntlem1.e
    pntlem1.k
    pntlem1.y
    pntlem1.x
    pntlem1.c
    pntlem1.w
    pntlem1.z
    pntlem1.m
    pntlem1.n
    pntlemg
    simp1d
    wph
    @32
    @48
    pntlem1.j
    cJ
    cM
    cN
    elfzouz
    syl
    cJ
    cM
    eluznn
    syl2anc
    nnnn0d
    expp1d
    eqtr4d
    breqtrd
    ltled
    wph
    @2
    @10
    cZ
    @36
    @34
    @26
    lediv2d
    mpbid
    @11
    @3
    flwordi
    syl3anc
    @12
    @4
    eluz2
    syl3anbrc
    @12
    @4
    eluzp1p1
    @5
    @13
    @7
    fzss1
    3syl
    wph
    @16
    @7
    cuz
    cfv
    wcel
    #
    @18
    @17
    wss
    wph
    @7
    cz
    wcel
    @16
    cz
    wcel
    @7
    @16
    cle
    wbr
    #
    @49
    wph
    @6
    wph
    @6
    wph
    cZ
    cV
    @26
    pntlem1.v
    rpdivcld
    rpred
    #
    flcld
    wph
    @15
    wph
    @15
    wph
    cZ
    @14
    @26
    @45
    rpdivcld
    rpred
    #
    flcld
    wph
    @6
    cr
    wcel
    @15
    cr
    wcel
    @6
    @15
    cle
    wbr
    #
    @50
    @51
    @52
    wph
    @14
    cV
    cle
    wbr
    @53
    wph
    @14
    cV
    wph
    @14
    @45
    rpred
    wph
    cV
    pntlem1.v
    rpred
    wph
    @40
    @41
    @43
    simpld
    ltled
    wph
    @14
    cV
    cZ
    @45
    pntlem1.v
    @26
    lediv2d
    mpbid
    @6
    @15
    flwordi
    syl3anc
    @7
    @16
    eluz2
    syl3anbrc
    @7
    @13
    @16
    fzss2
    syl
    sstrd
    pntlem1.i
    pntlem1.o
    3sstr4g
end
