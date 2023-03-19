include "c2.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "cv.mm"
include "clog.mm"
include "csu.mm"
include "cmul.mm"
include "c3.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "cexp.mm"
include "cr.mm"
include "wcel.mm"
include "2re.mm"
include "fzfid.mm"
include "wa.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "nndivred.mm"
include "fsumrecl.mm"
include "remulcl.mm"
include "sylancr.mm"
include "crp.mm"
include "clt.mm"
include "ceu.mm"
include "csqrt.mm"
include "w3a.mm"
include "c4.mm"
include "cmin.mm"
include "cdc.mm"
include "pntlemb.mm"
include "simp1d.mm"
include "peano2re.mm"
include "syl.mm"
include "resqcld.mm"
include "3re.mm"
include "readdcl.mm"
include "sylancl.mm"
include "remulcld.mm"
include "rpred.mm"
include "simpld.mm"
include "rerpdivcld.mm"
include "1red.mm"
include "rpsqrtcld.mm"
include "ere.mm"
include "a1i.mm"
include "1re.mm"
include "1lt2.mm"
include "egt2lt3.mm"
include "simpli.mm"
include "lttri.mm"
include "mp2an.mm"
include "ltleii.mm"
include "simp2d.mm"
include "letrd.mm"
include "simp3d.mm"
include "flge1nn.mm"
include "syl2anc.mm"
include "readdcld.mm"
include "logdivbnd.mm"
include "cc0.mm"
include "wb.mm"
include "2pos.mm"
include "lemuldiv2.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "reflcl.mm"
include "flle.mm"
include "simprd.mm"
include "1rp.mm"
include "lediv2d.mm"
include "mpbid.mm"
include "recnd.mm"
include "div1d.mm"
include "breqtrd.mm"
include "logled.mm"
include "leadd1dd.mm"
include "0red.mm"
include "log1.mm"
include "nnge1d.mm"
include "logleb.mm"
include "syl5eqbrr.mm"
include "lep1d.mm"
include "le2sqd.mm"
include "loge.mm"
include "rpge0d.mm"
include "lemulge12d.mm"
include "wceq.mm"
include "rprege0d.mm"
include "remsqsqrt.mm"
include "epr.mm"
include "leadd2dd.mm"
include "cc.mm"
include "binom21.mm"
include "sqvald.mm"
include "df-3.mm"
include "oveq1i.mm"
include "2cnd.mm"
include "1cnd.mm"
include "adddird.mm"
include "syl5eq.mm"
include "mulid2d.mm"
include "oveq2d.mm"
include "eqtr2d.mm"
include "oveq12d.mm"
include "sqcld.mm"
include "2cn.mm"
include "mulcl.mm"
include "addassd.mm"
include "3cn.mm"
include "3eqtr4rd.mm"
include "3brtr4d.mm"
include "lemul2d.mm"
include "wne.mm"
include "adantr.mm"
include "rpcnne0d.mm"
include "div23.mm"
include "divass.mm"
include "eqtr3d.mm"
include "syl3anc.mm"
include "sumeq2dv.mm"
include "fsummulc2.mm"
include "eqtr4d.mm"
include "mul12d.mm"
include "eqtrd.mm"
include "mulassd.mm"

theorem pntlemk
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

  disjoint C z
  disjoint n y
  disjoint n z
  disjoint y z
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
  disjoint u x
  disjoint L x
  disjoint K j
  disjoint K k
  disjoint K m
  disjoint K x
  disjoint M j
  disjoint M m
  disjoint M x
  disjoint O n
  disjoint O x
  disjoint O z
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
  assert |- ( ph -> ( 2 x. sum_ n e. ( 1 ... ( |_ ` ( Z / Y ) ) ) ( ( U / n ) x. ( log ` n ) ) ) <_ ( ( U x. ( ( log ` Z ) + 3 ) ) x. ( log ` Z ) ) )

  proof
    wph
    cU
    c2
    c1
    cZ
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
    vn
    cv
    #
    clog
    cfv
    #
    @3
    cdiv
    co
    #
    vn
    csu
    #
    cmul
    co
    #
    cmul
    co
    #
    cU
    cZ
    clog
    cfv
    #
    c3
    caddc
    co
    #
    @9
    cmul
    co
    #
    cmul
    co
    #
    c2
    @2
    cU
    @3
    cdiv
    co
    @4
    cmul
    co
    #
    vn
    csu
    #
    cmul
    co
    #
    cU
    @10
    cmul
    co
    @9
    cmul
    co
    cle
    wph
    @7
    @11
    cle
    wbr
    @8
    @12
    cle
    wbr
    wph
    @7
    @9
    c1
    caddc
    co
    #
    c2
    cexp
    co
    #
    @11
    wph
    c2
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    @7
    cr
    wcel
    2re
    wph
    @2
    @5
    vn
    wph
    c1
    @1
    fzfid
    #
    wph
    @3
    @2
    wcel
    #
    wa
    #
    @4
    @3
    @22
    @3
    @22
    @3
    @21
    @3
    cn
    wcel
    wph
    @3
    @1
    elfznn
    adantl
    #
    nnrpd
    #
    relogcld
    #
    @23
    nndivred
    #
    fsumrecl
    #
    c2
    @6
    remulcl
    sylancr
    #
    wph
    @16
    wph
    @9
    cr
    wcel
    #
    @16
    cr
    wcel
    wph
    cZ
    wph
    cZ
    crp
    wcel
    #
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
    @32
    @0
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
    @32
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
    @9
    @36
    cdiv
    co
    c4
    cdiv
    co
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
    @9
    cmul
    co
    cle
    wbr
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
    relogcld
    #
    @9
    peano2re
    syl
    #
    resqcld
    #
    wph
    @10
    @9
    wph
    @29
    c3
    cr
    wcel
    @10
    cr
    wcel
    @40
    3re
    @9
    c3
    readdcl
    sylancl
    #
    @40
    remulcld
    #
    wph
    @7
    @1
    clog
    cfv
    #
    c1
    caddc
    co
    #
    c2
    cexp
    co
    #
    @17
    @28
    wph
    @46
    wph
    @45
    c1
    wph
    @1
    wph
    @1
    wph
    @0
    cr
    wcel
    #
    c1
    @0
    cle
    wbr
    @1
    cn
    wcel
    #
    wph
    cZ
    cY
    wph
    cZ
    @39
    rpred
    #
    wph
    cY
    crp
    wcel
    #
    c1
    cY
    cle
    wbr
    #
    pntlem1.y
    simpld
    #
    rerpdivcld
    #
    wph
    c1
    @32
    @0
    wph
    1red
    #
    wph
    @32
    wph
    cZ
    @39
    rpsqrtcld
    #
    rpred
    #
    @54
    wph
    c1
    ceu
    @32
    @55
    ceu
    cr
    wcel
    wph
    ere
    a1i
    #
    @57
    c1
    ceu
    cle
    wbr
    wph
    c1
    ceu
    1re
    ere
    c1
    c2
    clt
    wbr
    c2
    ceu
    clt
    wbr
    #
    c1
    ceu
    clt
    wbr
    1lt2
    @59
    ceu
    c3
    clt
    wbr
    egt2lt3
    simpli
    c1
    c2
    ceu
    1re
    2re
    ere
    lttri
    mp2an
    ltleii
    a1i
    wph
    @31
    @33
    @34
    wph
    @30
    @35
    @37
    @38
    simp2d
    #
    simp2d
    #
    letrd
    #
    wph
    @31
    @33
    @34
    @60
    simp3d
    letrd
    @0
    flge1nn
    syl2anc
    #
    nnrpd
    #
    relogcld
    #
    @55
    readdcld
    #
    resqcld
    #
    @42
    wph
    @7
    @47
    cle
    wbr
    #
    @6
    @47
    c2
    cdiv
    co
    cle
    wbr
    #
    wph
    @49
    @69
    @63
    vn
    @1
    logdivbnd
    syl
    wph
    @19
    @47
    cr
    wcel
    @18
    cc0
    c2
    clt
    wbr
    #
    @68
    @69
    wb
    @27
    @67
    @18
    wph
    2re
    a1i
    #
    @70
    wph
    2pos
    a1i
    @6
    @47
    c2
    lemuldiv2
    syl112anc
    mpbird
    wph
    @46
    @16
    cle
    wbr
    @47
    @17
    cle
    wbr
    wph
    @45
    @9
    c1
    @65
    @40
    @55
    wph
    @1
    cZ
    cle
    wbr
    @45
    @9
    cle
    wbr
    wph
    @1
    @0
    cZ
    wph
    @48
    @1
    cr
    wcel
    @54
    @0
    reflcl
    syl
    @54
    @50
    wph
    @48
    @1
    @0
    cle
    wbr
    @54
    @0
    flle
    syl
    wph
    @0
    cZ
    c1
    cdiv
    co
    #
    cZ
    cle
    wph
    @52
    @0
    @72
    cle
    wbr
    wph
    @51
    @52
    pntlem1.y
    simprd
    wph
    c1
    cY
    cZ
    c1
    crp
    wcel
    #
    wph
    1rp
    a1i
    @53
    @39
    lediv2d
    mpbid
    wph
    cZ
    wph
    cZ
    @50
    recnd
    div1d
    breqtrd
    letrd
    wph
    @1
    cZ
    @64
    @39
    logled
    mpbid
    leadd1dd
    #
    wph
    @46
    @16
    @66
    @41
    wph
    cc0
    @45
    @46
    wph
    0red
    #
    @65
    @66
    wph
    cc0
    c1
    clog
    cfv
    #
    @45
    cle
    log1
    wph
    c1
    @1
    cle
    wbr
    #
    @76
    @45
    cle
    wbr
    #
    wph
    @1
    @63
    nnge1d
    wph
    @73
    @1
    crp
    wcel
    @77
    @78
    wb
    1rp
    @64
    c1
    @1
    logleb
    sylancr
    mpbid
    syl5eqbrr
    wph
    @45
    @65
    lep1d
    letrd
    #
    wph
    cc0
    @46
    @16
    @75
    @66
    @41
    @79
    @74
    letrd
    le2sqd
    mpbid
    letrd
    wph
    @9
    c2
    cexp
    co
    #
    c2
    @9
    cmul
    co
    #
    caddc
    co
    #
    c1
    caddc
    co
    #
    @82
    @9
    caddc
    co
    #
    @17
    @11
    cle
    wph
    c1
    @9
    @82
    @55
    @40
    wph
    @80
    @81
    wph
    @9
    @40
    resqcld
    wph
    c2
    @9
    @71
    @40
    remulcld
    readdcld
    wph
    c1
    ceu
    clog
    cfv
    #
    @9
    cle
    loge
    wph
    ceu
    cZ
    cle
    wbr
    #
    @85
    @9
    cle
    wbr
    #
    wph
    ceu
    @32
    cZ
    @58
    @57
    @50
    @61
    wph
    @32
    @32
    @32
    cmul
    co
    #
    cZ
    cle
    wph
    @32
    @32
    @57
    @57
    wph
    @32
    @56
    rpge0d
    @62
    lemulge12d
    wph
    cZ
    cr
    wcel
    cc0
    cZ
    cle
    wbr
    wa
    @88
    cZ
    wceq
    wph
    cZ
    @39
    rprege0d
    cZ
    remsqsqrt
    syl
    breqtrd
    letrd
    wph
    ceu
    crp
    wcel
    @30
    @86
    @87
    wb
    epr
    @39
    ceu
    cZ
    logleb
    sylancr
    mpbid
    syl5eqbrr
    leadd2dd
    wph
    @9
    cc
    wcel
    #
    @17
    @83
    wceq
    wph
    @9
    @40
    recnd
    #
    @9
    binom21
    syl
    wph
    @80
    @81
    @9
    caddc
    co
    #
    caddc
    co
    @9
    @9
    cmul
    co
    #
    c3
    @9
    cmul
    co
    #
    caddc
    co
    @84
    @11
    wph
    @80
    @92
    @91
    @93
    caddc
    wph
    @9
    @90
    sqvald
    wph
    @93
    @81
    c1
    @9
    cmul
    co
    #
    caddc
    co
    #
    @91
    wph
    @93
    c2
    c1
    caddc
    co
    #
    @9
    cmul
    co
    @95
    c3
    @96
    @9
    cmul
    df-3
    oveq1i
    wph
    c2
    c1
    @9
    wph
    2cnd
    #
    wph
    1cnd
    @90
    adddird
    syl5eq
    wph
    @94
    @9
    @81
    caddc
    wph
    @9
    @90
    mulid2d
    oveq2d
    eqtr2d
    oveq12d
    wph
    @80
    @81
    @9
    wph
    @9
    @90
    sqcld
    wph
    c2
    cc
    wcel
    @89
    @81
    cc
    wcel
    2cn
    @90
    c2
    @9
    mulcl
    sylancr
    @90
    addassd
    wph
    @9
    c3
    @9
    @90
    c3
    cc
    wcel
    wph
    3cn
    a1i
    @90
    adddird
    3eqtr4rd
    3brtr4d
    letrd
    wph
    @7
    @11
    cU
    @28
    @44
    pntlem1.u
    lemul2d
    mpbid
    wph
    @15
    c2
    cU
    @6
    cmul
    co
    #
    cmul
    co
    @8
    wph
    @14
    @98
    c2
    cmul
    wph
    @14
    @2
    cU
    @5
    cmul
    co
    #
    vn
    csu
    @98
    wph
    @2
    @13
    @99
    vn
    @22
    cU
    cc
    wcel
    #
    @4
    cc
    wcel
    #
    @3
    cc
    wcel
    @3
    cc0
    wne
    wa
    #
    @13
    @99
    wceq
    @22
    cU
    wph
    cU
    cr
    wcel
    @21
    wph
    cU
    pntlem1.u
    rpred
    #
    adantr
    recnd
    @22
    @4
    @25
    recnd
    @22
    @3
    @24
    rpcnne0d
    @100
    @101
    @102
    w3a
    cU
    @4
    cmul
    co
    @3
    cdiv
    co
    @13
    @99
    cU
    @4
    @3
    div23
    cU
    @4
    @3
    divass
    eqtr3d
    syl3anc
    sumeq2dv
    wph
    @2
    @5
    cU
    vn
    @20
    wph
    cU
    @103
    recnd
    #
    @22
    @5
    @26
    recnd
    fsummulc2
    eqtr4d
    oveq2d
    wph
    c2
    cU
    @6
    @97
    @104
    wph
    @6
    @27
    recnd
    mul12d
    eqtrd
    wph
    cU
    @10
    @9
    @104
    wph
    @10
    @43
    recnd
    @90
    mulassd
    3brtr4d
end
