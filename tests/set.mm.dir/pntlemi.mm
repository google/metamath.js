include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cexp.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cmul.mm"
include "caddc.mm"
include "cfv.mm"
include "cdiv.mm"
include "cabs.mm"
include "cle.mm"
include "cicc.mm"
include "wral.mm"
include "cmin.mm"
include "c8.mm"
include "clog.mm"
include "csu.mm"
include "crp.mm"
include "cpnf.mm"
include "cioo.mm"
include "wrex.mm"
include "cr.mm"
include "cz.mm"
include "cc0.mm"
include "w3a.mm"
include "pntlemc.mm"
include "simp2d.mm"
include "elfzoelz.mm"
include "rpexpcl.mm"
include "syl2an.mm"
include "rpred.mm"
include "csqrt.mm"
include "cfz.mm"
include "elfzofz.mm"
include "pntlemh.mm"
include "sylan2.mm"
include "simpld.mm"
include "cxr.mm"
include "wb.mm"
include "adantr.mm"
include "rpxr.mm"
include "elioopnf.mm"
include "3syl.mm"
include "mpbir2and.mm"
include "wceq.mm"
include "breq2.mm"
include "oveq2.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "id.mm"
include "oveq12d.mm"
include "raleqdv.mm"
include "cbvrexv.mm"
include "breq1.mm"
include "breq2d.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "rspcv.mm"
include "sylc.mm"
include "cfl.mm"
include "ad2antrr.mm"
include "cico.mm"
include "simprl.mm"
include "simprr.mm"
include "simplr.mm"
include "eqid.mm"
include "pntlemj.mm"
include "rexlimddv.mm"

theorem pntlemi
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
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vx: setvar x
  let vw: setvar w
  let cI: class I
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
  let cV: class V
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

  disjoint C z
  disjoint n y
  disjoint n z
  disjoint J n
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint n u
  disjoint L n
  disjoint u y
  disjoint u z
  disjoint L u
  disjoint L y
  disjoint L z
  disjoint K n
  disjoint K y
  disjoint K z
  disjoint M n
  disjoint M z
  disjoint O n
  disjoint O z
  disjoint n ph
  disjoint N n
  disjoint N z
  disjoint R n
  disjoint R u
  disjoint R y
  disjoint R z
  disjoint U n
  disjoint U z
  disjoint W n
  disjoint W z
  disjoint X n
  disjoint X y
  disjoint X z
  disjoint Y n
  disjoint Y z
  disjoint a n
  disjoint a u
  disjoint a y
  disjoint a z
  disjoint E a
  disjoint E n
  disjoint E u
  disjoint E y
  disjoint E z
  disjoint Z n
  disjoint Z u
  disjoint Z z
  disjoint x z
  disjoint C x
  disjoint F w
  disjoint I n
  disjoint n x
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
  disjoint u x
  disjoint L x
  disjoint K j
  disjoint K k
  disjoint K m
  disjoint K x
  disjoint M j
  disjoint M m
  disjoint M x
  disjoint O x
  disjoint j v
  disjoint j ph
  disjoint m v
  disjoint m ph
  disjoint n v
  disjoint v x
  disjoint ph v
  disjoint ph x
  disjoint N j
  disjoint N m
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
  disjoint V u
  disjoint U j
  disjoint U m
  disjoint U w
  disjoint U x
  disjoint W v
  disjoint W w
  disjoint X k
  disjoint Y i
  disjoint Y j
  disjoint Y m
  disjoint Y x
  disjoint a e
  disjoint a g
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a v
  disjoint a x
  disjoint E e
  disjoint E g
  disjoint E j
  disjoint E k
  disjoint E m
  disjoint E v
  disjoint E x
  disjoint Z j
  disjoint Z m
  disjoint Z x
  assert |- ( ( ph /\ J e. ( M ..^ N ) ) -> ( ( U - E ) x. ( ( ( L x. E ) / 8 ) x. ( log ` Z ) ) ) <_ sum_ n e. O ( ( ( U / n ) - ( abs ` ( ( R ` ( Z / n ) ) / Z ) ) ) x. ( log ` n ) ) )

  proof
    wph
    cJ
    cM
    cN
    cfzo
    co
    wcel
    #
    wa
    #
    cK
    cJ
    cexp
    co
    #
    vx
    cv
    #
    clt
    wbr
    #
    c1
    cL
    cE
    cmul
    co
    #
    caddc
    co
    #
    @3
    cmul
    co
    #
    cK
    @2
    cmul
    co
    #
    clt
    wbr
    #
    wa
    #
    vu
    cv
    #
    cR
    cfv
    @11
    cdiv
    co
    cabs
    cfv
    cE
    cle
    wbr
    #
    vu
    @3
    @7
    cicc
    co
    #
    wral
    #
    wa
    #
    cU
    cE
    cmin
    co
    #
    @5
    c8
    cdiv
    co
    cZ
    clog
    cfv
    cmul
    co
    cmul
    co
    cO
    cU
    vn
    cv
    #
    cdiv
    co
    cZ
    @17
    cdiv
    co
    cR
    cfv
    cZ
    cdiv
    co
    cabs
    cfv
    cmin
    co
    @17
    clog
    cfv
    cmul
    co
    vn
    csu
    cle
    wbr
    vx
    crp
    @1
    @2
    cX
    cpnf
    cioo
    co
    #
    wcel
    #
    vy
    cv
    #
    vz
    cv
    #
    clt
    wbr
    #
    @6
    @21
    cmul
    co
    #
    cK
    @20
    cmul
    co
    #
    clt
    wbr
    #
    wa
    #
    @12
    vu
    @21
    @23
    cicc
    co
    #
    wral
    #
    wa
    #
    vz
    crp
    wrex
    #
    vy
    @18
    wral
    #
    @15
    vx
    crp
    wrex
    #
    @1
    @19
    @2
    cr
    wcel
    #
    cX
    @2
    clt
    wbr
    #
    @1
    @2
    wph
    cK
    crp
    wcel
    #
    cJ
    cz
    wcel
    @2
    crp
    wcel
    @0
    wph
    cE
    crp
    wcel
    @35
    cE
    cc0
    c1
    cioo
    co
    #
    wcel
    c1
    cK
    clt
    wbr
    @16
    crp
    wcel
    w3a
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
    simp2d
    cJ
    cM
    cN
    elfzoelz
    cK
    cJ
    rpexpcl
    syl2an
    rpred
    @1
    @34
    @2
    cZ
    csqrt
    cfv
    cle
    wbr
    #
    @0
    wph
    cJ
    cM
    cN
    cfz
    co
    wcel
    @34
    @37
    wa
    cJ
    cM
    cN
    elfzofz
    wph
    cA
    cB
    cC
    cD
    cR
    cU
    cE
    cF
    cJ
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
    pntlemh
    sylan2
    simpld
    @1
    cX
    crp
    wcel
    #
    cX
    cxr
    wcel
    @19
    @33
    @34
    wa
    wb
    wph
    @38
    @0
    wph
    @38
    cY
    cX
    clt
    wbr
    #
    pntlem1.x
    simpld
    adantr
    cX
    rpxr
    cX
    @2
    elioopnf
    3syl
    mpbir2and
    wph
    @31
    @0
    pntlem1.K
    adantr
    @30
    @32
    vy
    @2
    @18
    @30
    @20
    @3
    clt
    wbr
    #
    @7
    @24
    clt
    wbr
    #
    wa
    #
    @14
    wa
    #
    vx
    crp
    wrex
    @20
    @2
    wceq
    #
    @32
    @29
    @43
    vz
    vx
    crp
    @21
    @3
    wceq
    #
    @26
    @42
    @28
    @14
    @45
    @22
    @40
    @25
    @41
    @21
    @3
    @20
    clt
    breq2
    @45
    @23
    @7
    @24
    clt
    @21
    @3
    @6
    cmul
    oveq2
    #
    breq1d
    anbi12d
    @45
    @12
    vu
    @27
    @13
    @45
    @21
    @3
    @23
    @7
    cicc
    @45
    id
    @46
    oveq12d
    raleqdv
    anbi12d
    cbvrexv
    @44
    @43
    @15
    vx
    crp
    @44
    @42
    @10
    @14
    @44
    @40
    @4
    @41
    @9
    @20
    @2
    @3
    clt
    breq1
    @44
    @24
    @8
    @7
    clt
    @20
    @2
    cK
    cmul
    oveq2
    breq2d
    anbi12d
    anbi1d
    rexbidv
    syl5bb
    rspcv
    sylc
    @1
    @3
    crp
    wcel
    #
    @15
    wa
    #
    wa
    vy
    vz
    vu
    cA
    cB
    cC
    cD
    cR
    cU
    vn
    cE
    cF
    cZ
    @7
    cdiv
    co
    cfl
    cfv
    c1
    caddc
    co
    cZ
    @3
    cdiv
    co
    cfl
    cfv
    cfz
    co
    #
    cJ
    cK
    cL
    cM
    cN
    cO
    @3
    cW
    cX
    cY
    cZ
    va
    pntlem1.r
    wph
    cA
    crp
    wcel
    @0
    @48
    pntlem1.a
    ad2antrr
    wph
    cB
    crp
    wcel
    @0
    @48
    pntlem1.b
    ad2antrr
    wph
    cL
    @36
    wcel
    @0
    @48
    pntlem1.l
    ad2antrr
    pntlem1.d
    pntlem1.f
    wph
    cU
    crp
    wcel
    @0
    @48
    pntlem1.u
    ad2antrr
    wph
    cU
    cA
    cle
    wbr
    @0
    @48
    pntlem1.u2
    ad2antrr
    pntlem1.e
    pntlem1.k
    wph
    cY
    crp
    wcel
    c1
    cY
    cle
    wbr
    wa
    @0
    @48
    pntlem1.y
    ad2antrr
    wph
    @38
    @39
    wa
    @0
    @48
    pntlem1.x
    ad2antrr
    wph
    cC
    crp
    wcel
    @0
    @48
    pntlem1.c
    ad2antrr
    pntlem1.w
    wph
    cZ
    cW
    cpnf
    cico
    co
    wcel
    @0
    @48
    pntlem1.z
    ad2antrr
    pntlem1.m
    pntlem1.n
    wph
    @21
    cR
    cfv
    @21
    cdiv
    co
    cabs
    cfv
    cU
    cle
    wbr
    vz
    cY
    cpnf
    cico
    co
    wral
    @0
    @48
    pntlem1.U
    ad2antrr
    wph
    @31
    @0
    @48
    pntlem1.K
    ad2antrr
    pntlem1.o
    @1
    @47
    @15
    simprl
    @1
    @47
    @15
    simprr
    wph
    @0
    @48
    simplr
    @49
    eqid
    pntlemj
    rexlimddv
end
