include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cabs.mm"
include "c3.mm"
include "cexp.mm"
include "cmul.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "clog.mm"
include "caddc.mm"
include "c2.mm"
include "cdc.mm"
include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "c1.mm"
include "clt.mm"
include "ceu.mm"
include "csqrt.mm"
include "w3a.mm"
include "c4.mm"
include "pntlemb.mm"
include "simp1d.mm"
include "pntrf.mm"
include "ffvelrni.mm"
include "syl.mm"
include "rerpdivcld.mm"
include "recnd.mm"
include "abscld.mm"
include "relogcld.mm"
include "remulcld.mm"
include "rpred.mm"
include "3re.mm"
include "a1i.mm"
include "readdcld.mm"
include "2re.mm"
include "cc0.mm"
include "cioo.mm"
include "pntlemc.mm"
include "simp3d.mm"
include "pntlemd.mm"
include "cz.mm"
include "2z.mm"
include "rpexpcl.mm"
include "sylancl.mm"
include "rpmulcld.mm"
include "cn.mm"
include "3nn0.mm"
include "2nn.mm"
include "decnncl.mm"
include "nnrp.mm"
include "ax-mp.mm"
include "rpmulcl.mm"
include "sylancr.mm"
include "rpdivcld.mm"
include "resubcld.mm"
include "rpcnd.mm"
include "subdird.mm"
include "cc.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "rpcnne0d.mm"
include "div23.mm"
include "syl3anc.mm"
include "oveq1i.mm"
include "simp2d.mm"
include "rpne0d.mm"
include "sqdivd.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "sqcld.mm"
include "divass.mm"
include "eqtr3d.mm"
include "3eqtrd.mm"
include "df-3.mm"
include "oveq2i.mm"
include "cn0.mm"
include "2nn0.mm"
include "expp1.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "mulassd.mm"
include "1cnd.mm"
include "rpreccld.mm"
include "mulid2d.mm"
include "divrec2d.mm"
include "syl5req.mm"
include "oveq12d.mm"
include "eqtr2d.mm"
include "oveq1d.mm"
include "subcld.mm"
include "mul32d.mm"
include "eqtr4d.mm"
include "3eqtr2d.mm"
include "eqeltrrd.mm"
include "cfl.mm"
include "cfz.mm"
include "cv.mm"
include "csu.mm"
include "rplogcld.mm"
include "fzfid.mm"
include "adantr.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnrpd.mm"
include "fsumrecl.mm"
include "mulcld.mm"
include "divsubdird.mm"
include "div23d.mm"
include "absdivd.mm"
include "rprege0d.mm"
include "absid.mm"
include "divassd.mm"
include "sumeq2dv.mm"
include "fsumdivc.mm"
include "cpnf.mm"
include "wral.mm"
include "cxr.mm"
include "wb.mm"
include "1re.mm"
include "rexr.mm"
include "elioopnf.mm"
include "mp2b.mm"
include "sylanbrc.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "cbvsumv.mm"
include "oveq1.mm"
include "simpl.mm"
include "sumeq12rdv.mm"
include "id.mm"
include "breq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqbrtrrd.mm"
include "lesubadd2d.mm"
include "mpbid.mm"
include "2cnd.mm"
include "fsumcl.mm"
include "resqcld.mm"
include "remulcl.mm"
include "nndivred.mm"
include "pntlemf.mm"
include "2pos.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "fsumsub.mm"
include "subdid.mm"
include "pntlemk.mm"
include "lesub1dd.mm"
include "eqbrtrd.mm"
include "letrd.mm"
include "lesubd.mm"
include "sqvald.mm"
include "breqtrrd.mm"
include "ledivmul2d.mm"
include "mpbird.mm"
include "leadd1dd.mm"
include "leadd2dd.mm"
include "adddid.mm"
include "addassd.mm"
include "2timesd.mm"
include "nppcan3d.mm"
include "3brtr4d.mm"
include "lesubaddd.mm"
include "addsubd.mm"
include "3brtr3d.mm"
include "3z.mm"
include "lemul1d.mm"

theorem pntlemo
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
  let vi: setvar i
  let cE: class E
  let cF: class F
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vx: setvar x
  let vw: setvar w
  let cI: class I
  let vn: setvar n
  let cJ: class J
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cO: class O
  let vv: setvar v
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
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
  assume pntlem1.C: |- ( ph -> A. z e. ( 1 (,) +oo ) ( ( ( ( abs ` ( R ` z ) ) x. ( log ` z ) ) - ( ( 2 / ( log ` z ) ) x. sum_ i e. ( 1 ... ( |_ ` ( z / Y ) ) ) ( ( abs ` ( R ` ( z / i ) ) ) x. ( log ` i ) ) ) ) / z ) <_ C )

  disjoint C z
  disjoint y z
  disjoint u y
  disjoint u z
  disjoint L u
  disjoint L y
  disjoint L z
  disjoint K y
  disjoint K z
  disjoint M z
  disjoint N z
  disjoint i u
  disjoint i y
  disjoint i z
  disjoint R i
  disjoint R u
  disjoint R y
  disjoint R z
  disjoint U z
  disjoint W z
  disjoint X y
  disjoint X z
  disjoint Y i
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
  disjoint J y
  disjoint J z
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
  disjoint O z
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
  disjoint i v
  disjoint i w
  disjoint i x
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
  disjoint V u
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
  assert |- ( ph -> ( abs ` ( ( R ` Z ) / Z ) ) <_ ( U - ( F x. ( U ^ 3 ) ) ) )

  proof
    wph
    cZ
    cR
    cfv
    #
    cZ
    cdiv
    co
    #
    cabs
    cfv
    #
    cU
    cF
    cU
    c3
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cle
    wbr
    @2
    cZ
    clog
    cfv
    #
    cmul
    co
    #
    @5
    @6
    cmul
    co
    #
    cle
    wbr
    wph
    @7
    cU
    @6
    c3
    caddc
    co
    #
    cmul
    co
    #
    c2
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
    #
    cmul
    co
    #
    c3
    c2
    cdc
    #
    cB
    cmul
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    @6
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cC
    caddc
    co
    #
    @8
    wph
    @2
    @6
    wph
    @1
    wph
    @1
    wph
    @0
    cZ
    wph
    cZ
    crp
    wcel
    #
    @0
    cr
    wcel
    wph
    @22
    c1
    cZ
    clt
    wbr
    #
    ceu
    cZ
    csqrt
    cfv
    #
    cle
    wbr
    #
    @24
    cZ
    cY
    cdiv
    co
    #
    cle
    wbr
    #
    w3a
    #
    c4
    cL
    cE
    cmul
    co
    cdiv
    co
    @24
    cle
    wbr
    #
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
    @6
    @30
    cdiv
    co
    c4
    cdiv
    co
    cle
    wbr
    #
    cU
    c3
    cmul
    co
    #
    cC
    caddc
    co
    #
    @18
    cle
    wbr
    #
    w3a
    #
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
    #
    simp1d
    #
    crp
    cr
    cZ
    cR
    cR
    va
    pntlem1.r
    pntrf
    #
    ffvelrni
    syl
    #
    @37
    rerpdivcld
    recnd
    abscld
    #
    wph
    cZ
    @37
    relogcld
    #
    remulcld
    #
    wph
    @20
    cC
    wph
    @10
    @19
    wph
    cU
    @9
    wph
    cU
    pntlem1.u
    rpred
    #
    wph
    @6
    c3
    @41
    c3
    cr
    wcel
    #
    wph
    3re
    a1i
    #
    readdcld
    remulcld
    #
    wph
    c2
    @18
    c2
    cr
    wcel
    #
    wph
    2re
    a1i
    #
    wph
    @17
    @6
    wph
    @11
    @16
    wph
    @11
    wph
    cE
    cc0
    c1
    cioo
    co
    wcel
    #
    c1
    cK
    clt
    wbr
    #
    @11
    crp
    wcel
    #
    wph
    cE
    crp
    wcel
    #
    cK
    crp
    wcel
    #
    @49
    @50
    @51
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
    simp3d
    simp3d
    #
    rpred
    #
    wph
    @16
    wph
    @13
    @15
    wph
    cL
    @12
    wph
    cL
    crp
    wcel
    #
    cD
    crp
    wcel
    #
    cF
    crp
    wcel
    #
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
    #
    simp1d
    #
    wph
    @52
    c2
    cz
    wcel
    #
    @12
    crp
    wcel
    wph
    @52
    @53
    @54
    @55
    simp1d
    2z
    cE
    c2
    rpexpcl
    sylancl
    #
    rpmulcld
    wph
    @14
    crp
    wcel
    #
    cB
    crp
    wcel
    @15
    crp
    wcel
    @14
    cn
    wcel
    @65
    c3
    c2
    3nn0
    2nn
    decnncl
    @14
    nnrp
    ax-mp
    pntlem1.b
    @14
    cB
    rpmulcl
    sylancr
    #
    rpdivcld
    #
    rpred
    #
    remulcld
    #
    @41
    remulcld
    #
    remulcld
    #
    resubcld
    #
    wph
    cC
    pntlem1.c
    rpred
    #
    readdcld
    #
    wph
    cU
    @6
    cmul
    co
    #
    @18
    cmin
    co
    #
    @8
    cr
    wph
    cU
    @17
    cmin
    co
    #
    @6
    cmul
    co
    @76
    @8
    wph
    cU
    @17
    @6
    wph
    cU
    pntlem1.u
    rpcnd
    #
    wph
    @17
    @69
    recnd
    #
    wph
    @6
    @41
    recnd
    #
    subdird
    wph
    @77
    @5
    @6
    cmul
    wph
    @17
    @4
    cU
    cmin
    wph
    @17
    @11
    cL
    @15
    cdiv
    co
    #
    cD
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cU
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    @4
    wph
    @16
    @85
    @11
    cmul
    wph
    @16
    @81
    @12
    cmul
    co
    #
    @81
    @84
    @82
    cdiv
    co
    #
    cmul
    co
    #
    @85
    wph
    cL
    cc
    wcel
    @12
    cc
    wcel
    @15
    cc
    wcel
    @15
    cc0
    wne
    wa
    @16
    @87
    wceq
    wph
    cL
    @62
    rpcnd
    wph
    @12
    @64
    rpcnd
    wph
    @15
    @66
    rpcnne0d
    cL
    @12
    @15
    div23
    syl3anc
    wph
    @12
    @88
    @81
    cmul
    wph
    @12
    cU
    cD
    cdiv
    co
    #
    c2
    cexp
    co
    @88
    cE
    @90
    c2
    cexp
    pntlem1.e
    oveq1i
    wph
    cU
    cD
    @78
    wph
    cD
    wph
    @58
    @59
    @60
    @61
    simp2d
    #
    rpcnd
    #
    wph
    cD
    @91
    rpne0d
    #
    sqdivd
    syl5eq
    oveq2d
    wph
    @81
    cc
    wcel
    #
    @84
    cc
    wcel
    #
    @82
    cc
    wcel
    @82
    cc0
    wne
    wa
    #
    @89
    @85
    wceq
    wph
    @81
    wph
    cL
    @15
    @62
    @66
    rpdivcld
    #
    rpcnd
    wph
    cU
    @78
    sqcld
    #
    wph
    @82
    wph
    @59
    @63
    @82
    crp
    wcel
    @91
    2z
    cD
    c2
    rpexpcl
    sylancl
    #
    rpcnne0d
    @94
    @95
    @96
    w3a
    @81
    @84
    cmul
    co
    @82
    cdiv
    co
    @89
    @85
    @81
    @84
    @82
    divass
    @81
    @84
    @82
    div23
    eqtr3d
    syl3anc
    3eqtrd
    oveq2d
    wph
    @4
    cF
    cU
    @84
    cmul
    co
    #
    cmul
    co
    cF
    cU
    cmul
    co
    #
    @84
    cmul
    co
    #
    @86
    wph
    @3
    @100
    cF
    cmul
    wph
    @3
    @84
    cU
    cmul
    co
    #
    @100
    wph
    @3
    cU
    c2
    c1
    caddc
    co
    #
    cexp
    co
    #
    @103
    c3
    @104
    cU
    cexp
    df-3
    oveq2i
    wph
    cU
    cc
    wcel
    c2
    cn0
    wcel
    @105
    @103
    wceq
    @78
    2nn0
    cU
    c2
    expp1
    sylancl
    syl5eq
    wph
    @84
    cU
    @98
    @78
    mulcomd
    eqtrd
    oveq2d
    wph
    cF
    cU
    @84
    wph
    cF
    wph
    @58
    @59
    @60
    @61
    simp3d
    #
    rpcnd
    @78
    @98
    mulassd
    wph
    @11
    @83
    cmul
    co
    #
    @84
    cmul
    co
    @102
    @86
    wph
    @107
    @101
    @84
    cmul
    wph
    @107
    c1
    c1
    cD
    cdiv
    co
    #
    cmin
    co
    #
    cU
    cmul
    co
    #
    @83
    cmul
    co
    #
    @101
    wph
    @11
    @110
    @83
    cmul
    wph
    @110
    c1
    cU
    cmul
    co
    #
    @108
    cU
    cmul
    co
    #
    cmin
    co
    @11
    wph
    c1
    @108
    cU
    wph
    1cnd
    #
    wph
    @108
    wph
    cD
    @91
    rpreccld
    rpcnd
    #
    @78
    subdird
    wph
    @112
    cU
    @113
    cE
    cmin
    wph
    cU
    @78
    mulid2d
    wph
    cE
    @90
    @113
    pntlem1.e
    wph
    cU
    cD
    @78
    @92
    @93
    divrec2d
    syl5req
    oveq12d
    eqtr2d
    oveq1d
    wph
    @101
    @109
    @83
    cmul
    co
    #
    cU
    cmul
    co
    @111
    cF
    @116
    cU
    cmul
    pntlem1.f
    oveq1i
    wph
    @109
    @83
    cU
    wph
    c1
    @108
    @114
    @115
    subcld
    wph
    @83
    wph
    @81
    @82
    @97
    @99
    rpdivcld
    rpcnd
    #
    @78
    mul32d
    syl5eq
    eqtr4d
    oveq1d
    wph
    @11
    @83
    @84
    wph
    @11
    @56
    rpcnd
    #
    @117
    @98
    mulassd
    eqtr3d
    3eqtr2d
    eqtr4d
    oveq2d
    oveq1d
    eqtr3d
    #
    wph
    @75
    @18
    wph
    cU
    @6
    @43
    @41
    remulcld
    #
    @70
    resubcld
    #
    eqeltrrd
    wph
    @7
    c2
    @6
    cdiv
    co
    #
    c1
    @26
    cfl
    cfv
    #
    cfz
    co
    #
    cZ
    vn
    cv
    #
    cdiv
    co
    #
    cR
    cfv
    #
    cZ
    cdiv
    co
    #
    cabs
    cfv
    #
    @125
    clog
    cfv
    #
    cmul
    co
    #
    vn
    csu
    #
    cmul
    co
    #
    cC
    caddc
    co
    #
    @21
    @42
    wph
    @133
    cC
    wph
    @122
    @132
    wph
    c2
    @6
    @48
    wph
    cZ
    wph
    cZ
    @37
    rpred
    #
    wph
    @23
    @25
    @27
    wph
    @22
    @28
    @35
    @36
    simp2d
    simp1d
    #
    rplogcld
    #
    rerpdivcld
    #
    wph
    @124
    @131
    vn
    wph
    c1
    @123
    fzfid
    #
    wph
    @125
    @124
    wcel
    #
    wa
    #
    @129
    @130
    @141
    @128
    @141
    @128
    @141
    @127
    cZ
    @141
    @126
    crp
    wcel
    @127
    cr
    wcel
    @141
    cZ
    @125
    wph
    @22
    @140
    @37
    adantr
    #
    @141
    @125
    @140
    @125
    cn
    wcel
    wph
    @125
    @123
    elfznn
    adantl
    #
    nnrpd
    #
    rpdivcld
    crp
    cr
    @126
    cR
    @38
    ffvelrni
    syl
    #
    @142
    rerpdivcld
    recnd
    abscld
    #
    @141
    @125
    @144
    relogcld
    #
    remulcld
    fsumrecl
    #
    remulcld
    #
    @73
    readdcld
    @74
    wph
    @7
    @133
    cmin
    co
    #
    cC
    cle
    wbr
    @7
    @134
    cle
    wbr
    wph
    @0
    cabs
    cfv
    #
    @6
    cmul
    co
    #
    @122
    @124
    @127
    cabs
    cfv
    #
    @130
    cmul
    co
    #
    vn
    csu
    #
    cmul
    co
    #
    cmin
    co
    #
    cZ
    cdiv
    co
    #
    @150
    cC
    cle
    wph
    @158
    @152
    cZ
    cdiv
    co
    #
    @156
    cZ
    cdiv
    co
    #
    cmin
    co
    @150
    wph
    @152
    @156
    cZ
    wph
    @151
    @6
    wph
    @151
    wph
    @0
    wph
    @0
    @39
    recnd
    #
    abscld
    recnd
    #
    @80
    mulcld
    wph
    @122
    @155
    wph
    @122
    @138
    recnd
    #
    wph
    @155
    wph
    @124
    @154
    vn
    @139
    @141
    @153
    @130
    @141
    @127
    @141
    @127
    @145
    recnd
    #
    abscld
    #
    @147
    remulcld
    #
    fsumrecl
    recnd
    #
    mulcld
    wph
    cZ
    @37
    rpcnd
    #
    wph
    cZ
    @37
    rpne0d
    #
    divsubdird
    wph
    @159
    @7
    @160
    @133
    cmin
    wph
    @159
    @151
    cZ
    cdiv
    co
    #
    @6
    cmul
    co
    @7
    wph
    @151
    @6
    cZ
    @162
    @80
    @168
    @169
    div23d
    wph
    @2
    @170
    @6
    cmul
    wph
    @2
    @151
    cZ
    cabs
    cfv
    #
    cdiv
    co
    @170
    wph
    @0
    cZ
    @161
    @168
    @169
    absdivd
    wph
    @171
    cZ
    @151
    cdiv
    wph
    cZ
    cr
    wcel
    #
    cc0
    cZ
    cle
    wbr
    wa
    @171
    cZ
    wceq
    #
    wph
    cZ
    @37
    rprege0d
    cZ
    absid
    syl
    #
    oveq2d
    eqtrd
    oveq1d
    eqtr4d
    wph
    @160
    @122
    @155
    cZ
    cdiv
    co
    #
    cmul
    co
    @133
    wph
    @122
    @155
    cZ
    @163
    @167
    @168
    @169
    divassd
    wph
    @132
    @175
    @122
    cmul
    wph
    @132
    @124
    @154
    cZ
    cdiv
    co
    #
    vn
    csu
    @175
    wph
    @124
    @131
    @176
    vn
    @141
    @131
    @153
    cZ
    cdiv
    co
    #
    @130
    cmul
    co
    #
    @176
    @141
    @129
    @177
    @130
    cmul
    @141
    @129
    @153
    @171
    cdiv
    co
    @177
    @141
    @127
    cZ
    @164
    wph
    cZ
    cc
    wcel
    #
    @140
    @168
    adantr
    wph
    cZ
    cc0
    wne
    #
    @140
    @169
    adantr
    absdivd
    @141
    @171
    cZ
    @153
    cdiv
    wph
    @173
    @140
    @174
    adantr
    oveq2d
    eqtrd
    oveq1d
    @141
    @153
    cc
    wcel
    @130
    cc
    wcel
    @179
    @180
    wa
    #
    @176
    @178
    wceq
    @141
    @153
    @165
    recnd
    @141
    @130
    @147
    recnd
    #
    wph
    @181
    @140
    wph
    cZ
    @37
    rpcnne0d
    adantr
    @153
    @130
    cZ
    div23
    syl3anc
    eqtr4d
    sumeq2dv
    wph
    @124
    @154
    cZ
    vn
    @139
    @168
    @141
    @154
    @166
    recnd
    @169
    fsumdivc
    eqtr4d
    oveq2d
    eqtr4d
    oveq12d
    eqtrd
    wph
    cZ
    c1
    cpnf
    cioo
    co
    #
    wcel
    #
    vz
    cv
    #
    cR
    cfv
    #
    cabs
    cfv
    #
    @185
    clog
    cfv
    #
    cmul
    co
    #
    c2
    @188
    cdiv
    co
    #
    c1
    @185
    cY
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    @185
    vi
    cv
    #
    cdiv
    co
    #
    cR
    cfv
    #
    cabs
    cfv
    #
    @194
    clog
    cfv
    #
    cmul
    co
    #
    vi
    csu
    #
    cmul
    co
    #
    cmin
    co
    #
    @185
    cdiv
    co
    #
    cC
    cle
    wbr
    #
    vz
    @183
    wral
    @158
    cC
    cle
    wbr
    #
    wph
    @172
    @23
    @184
    @135
    @136
    c1
    cr
    wcel
    c1
    cxr
    wcel
    @184
    @172
    @23
    wa
    wb
    1re
    c1
    rexr
    c1
    cZ
    elioopnf
    mp2b
    sylanbrc
    pntlem1.C
    @204
    @205
    vz
    cZ
    @183
    @185
    cZ
    wceq
    #
    @203
    @158
    cC
    cle
    @206
    @202
    @157
    @185
    cZ
    cdiv
    @206
    @189
    @152
    @201
    @156
    cmin
    @206
    @187
    @151
    @188
    @6
    cmul
    @206
    @186
    @0
    cabs
    @185
    cZ
    cR
    fveq2
    fveq2d
    @185
    cZ
    clog
    fveq2
    #
    oveq12d
    @206
    @190
    @122
    @200
    @155
    cmul
    @206
    @188
    @6
    c2
    cdiv
    @207
    oveq2d
    @206
    @200
    @193
    @185
    @125
    cdiv
    co
    #
    cR
    cfv
    #
    cabs
    cfv
    #
    @130
    cmul
    co
    #
    vn
    csu
    @155
    @193
    @199
    @211
    vi
    vn
    @194
    @125
    wceq
    #
    @197
    @210
    @198
    @130
    cmul
    @212
    @196
    @209
    cabs
    @212
    @195
    @208
    cR
    @194
    @125
    @185
    cdiv
    oveq2
    fveq2d
    fveq2d
    @194
    @125
    clog
    fveq2
    oveq12d
    cbvsumv
    @206
    @193
    @124
    @211
    @154
    vn
    @206
    @192
    @123
    c1
    cfz
    @206
    @191
    @26
    cfl
    @185
    cZ
    cY
    cdiv
    oveq1
    fveq2d
    oveq2d
    @206
    @140
    wa
    #
    @210
    @153
    @130
    cmul
    @213
    @209
    @127
    cabs
    @213
    @208
    @126
    cR
    @213
    @185
    cZ
    @125
    cdiv
    @206
    @140
    simpl
    oveq1d
    fveq2d
    fveq2d
    oveq1d
    sumeq12rdv
    syl5eq
    oveq12d
    oveq12d
    @206
    id
    oveq12d
    breq1d
    rspcv
    sylc
    eqbrtrrd
    wph
    @7
    @133
    cC
    @42
    @149
    @73
    lesubadd2d
    mpbid
    wph
    @133
    @20
    cC
    @149
    @72
    @73
    wph
    c2
    @132
    cmul
    co
    #
    @6
    cdiv
    co
    #
    @133
    @20
    cle
    wph
    c2
    @132
    @6
    wph
    2cnd
    #
    wph
    @124
    @131
    vn
    @139
    @141
    @129
    @130
    @141
    @129
    @146
    recnd
    #
    @182
    mulcld
    #
    fsumcl
    #
    @80
    wph
    @6
    @137
    rpne0d
    div23d
    wph
    @215
    @20
    cle
    wbr
    @214
    @20
    @6
    cmul
    co
    #
    cle
    wbr
    wph
    @214
    @10
    @6
    cmul
    co
    #
    c2
    @11
    @16
    @6
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    @220
    cle
    wph
    @225
    @221
    @214
    wph
    @47
    @224
    cr
    wcel
    #
    @225
    cr
    wcel
    2re
    wph
    @11
    @223
    @57
    wph
    @16
    @222
    @68
    wph
    @6
    @41
    resqcld
    #
    remulcld
    remulcld
    #
    c2
    @224
    remulcl
    sylancr
    #
    wph
    @10
    @6
    @46
    @41
    remulcld
    #
    wph
    @47
    @132
    cr
    wcel
    @214
    cr
    wcel
    2re
    @148
    c2
    @132
    remulcl
    sylancr
    #
    wph
    @225
    c2
    @124
    cU
    @125
    cdiv
    co
    #
    @129
    cmin
    co
    #
    @130
    cmul
    co
    #
    vn
    csu
    #
    cmul
    co
    #
    @221
    @214
    cmin
    co
    #
    @230
    wph
    c2
    @236
    @48
    wph
    @124
    @235
    vn
    @139
    @141
    @234
    @130
    @141
    @233
    @129
    @141
    cU
    @125
    wph
    cU
    cr
    wcel
    #
    @140
    @43
    adantr
    @143
    nndivred
    #
    @146
    resubcld
    @147
    remulcld
    fsumrecl
    #
    remulcld
    wph
    @221
    @214
    @231
    @232
    resubcld
    wph
    @224
    @236
    cle
    wbr
    #
    @225
    @237
    cle
    wbr
    #
    wph
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
    pntlem1.U
    pntlem1.K
    pntlemf
    wph
    @227
    @236
    cr
    wcel
    @47
    cc0
    c2
    clt
    wbr
    #
    @242
    @243
    wb
    @229
    @241
    @48
    @244
    wph
    2pos
    a1i
    @224
    @236
    c2
    lemul2
    syl112anc
    mpbid
    wph
    @237
    c2
    @124
    @233
    @130
    cmul
    co
    #
    vn
    csu
    #
    cmul
    co
    #
    @214
    cmin
    co
    #
    @238
    cle
    wph
    @237
    c2
    @246
    @132
    cmin
    co
    #
    cmul
    co
    @248
    wph
    @236
    @249
    c2
    cmul
    wph
    @236
    @124
    @245
    @131
    cmin
    co
    #
    vn
    csu
    @249
    wph
    @124
    @235
    @250
    vn
    @141
    @233
    @129
    @130
    @141
    @233
    @240
    recnd
    @217
    @182
    subdird
    sumeq2dv
    wph
    @124
    @245
    @131
    vn
    @139
    @141
    @245
    @141
    @233
    @130
    @240
    @147
    remulcld
    #
    recnd
    @218
    fsumsub
    eqtrd
    oveq2d
    wph
    c2
    @246
    @132
    @216
    wph
    @246
    wph
    @124
    @245
    vn
    @139
    @251
    fsumrecl
    #
    recnd
    @219
    subdid
    eqtrd
    wph
    @247
    @221
    @214
    wph
    @47
    @246
    cr
    wcel
    @247
    cr
    wcel
    2re
    @252
    c2
    @246
    remulcl
    sylancr
    @231
    @232
    wph
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
    pntlem1.U
    pntlem1.K
    pntlemk
    lesub1dd
    eqbrtrd
    letrd
    lesubd
    wph
    @220
    @221
    @19
    @6
    cmul
    co
    #
    cmin
    co
    @226
    wph
    @10
    @19
    @6
    wph
    @10
    @46
    recnd
    #
    wph
    @19
    @71
    recnd
    #
    @80
    subdird
    wph
    @253
    @225
    @221
    cmin
    wph
    @253
    c2
    @18
    @6
    cmul
    co
    #
    cmul
    co
    @225
    wph
    c2
    @18
    @6
    @216
    wph
    @18
    @70
    recnd
    #
    @80
    mulassd
    wph
    @256
    @224
    c2
    cmul
    wph
    @256
    @17
    @6
    @6
    cmul
    co
    #
    cmul
    co
    @17
    @222
    cmul
    co
    @224
    wph
    @17
    @6
    @6
    @79
    @80
    @80
    mulassd
    wph
    @222
    @258
    @17
    cmul
    wph
    @6
    @80
    sqvald
    oveq2d
    wph
    @11
    @16
    @222
    @118
    wph
    @16
    @67
    rpcnd
    wph
    @222
    @228
    recnd
    mulassd
    3eqtr2d
    oveq2d
    eqtrd
    oveq2d
    eqtrd
    breqtrrd
    wph
    @214
    @20
    @6
    @232
    @72
    @137
    ledivmul2d
    mpbird
    eqbrtrrd
    leadd1dd
    letrd
    wph
    @10
    cC
    caddc
    co
    #
    @19
    cmin
    co
    #
    @76
    @21
    @8
    cle
    wph
    @260
    @76
    cle
    wbr
    @259
    @76
    @19
    caddc
    co
    #
    cle
    wbr
    wph
    @75
    @33
    caddc
    co
    #
    @75
    @18
    caddc
    co
    #
    @259
    @261
    cle
    wph
    @33
    @18
    @75
    wph
    @32
    cC
    wph
    @239
    @44
    @32
    cr
    wcel
    @43
    3re
    cU
    c3
    remulcl
    sylancl
    @73
    readdcld
    @70
    @120
    wph
    @29
    @31
    @34
    wph
    @22
    @28
    @35
    @36
    simp3d
    simp3d
    leadd2dd
    wph
    @259
    @75
    @32
    caddc
    co
    #
    cC
    caddc
    co
    @262
    wph
    @10
    @264
    cC
    caddc
    wph
    cU
    @6
    c3
    @78
    @80
    wph
    c3
    @45
    recnd
    #
    adddid
    oveq1d
    wph
    @75
    @32
    cC
    wph
    @75
    @120
    recnd
    #
    wph
    cU
    c3
    @78
    @265
    mulcld
    wph
    cC
    pntlem1.c
    rpcnd
    #
    addassd
    eqtrd
    wph
    @261
    @76
    @18
    @18
    caddc
    co
    #
    caddc
    co
    @263
    wph
    @19
    @268
    @76
    caddc
    wph
    @18
    @257
    2timesd
    oveq2d
    wph
    @75
    @18
    @18
    @266
    @257
    @257
    nppcan3d
    eqtrd
    3brtr4d
    wph
    @259
    @19
    @76
    wph
    @10
    cC
    @46
    @73
    readdcld
    @71
    @121
    lesubaddd
    mpbird
    wph
    @10
    cC
    @19
    @254
    @267
    @255
    addsubd
    @119
    3brtr3d
    letrd
    wph
    @2
    @5
    @6
    @40
    wph
    cU
    @4
    @43
    wph
    @4
    wph
    cF
    @3
    @106
    wph
    cU
    crp
    wcel
    c3
    cz
    wcel
    @3
    crp
    wcel
    pntlem1.u
    3z
    cU
    c3
    rpexpcl
    sylancl
    rpmulcld
    rpred
    resubcld
    @137
    lemul1d
    mpbird
end
