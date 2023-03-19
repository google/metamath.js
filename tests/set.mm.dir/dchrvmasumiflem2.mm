include "crp.mm"
include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cmu.mm"
include "cdiv.mm"
include "cmul.mm"
include "cc0.mm"
include "wceq.mm"
include "cif.mm"
include "clog.mm"
include "csu.mm"
include "cvma.mm"
include "caddc.mm"
include "cc.mm"
include "1red.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wa.mm"
include "fzfid.mm"
include "ad2antrr.mm"
include "cz.mm"
include "elfzelz.mm"
include "adantl.mm"
include "dchrzrhcl.mm"
include "cn.mm"
include "elfznn.mm"
include "mucl.mm"
include "syl.mm"
include "zred.mm"
include "nndivred.mm"
include "recnd.mm"
include "mulcld.mm"
include "fsumcl.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "climcl.mm"
include "adantr.mm"
include "0cnd.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "simpr.mm"
include "divcld.mm"
include "sylan2br.mm"
include "ifclda.mm"
include "dchrmusum2.mm"
include "cr.mm"
include "wss.mm"
include "rpssre.mm"
include "o1const.mm"
include "sylancr.mm"
include "o1mul2.mm"
include "nnrpd.mm"
include "rpdivcl.mm"
include "syl2an.mm"
include "ifcl.mm"
include "relogcld.mm"
include "cmin.mm"
include "0cn.mm"
include "subdid.mm"
include "sumeq2dv.mm"
include "fsumsub.mm"
include "mulassd.mm"
include "ovif2.mm"
include "mul01d.mm"
include "ifeq1d.mm"
include "divcan2d.mm"
include "ifeq2da.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "fsummulc1.mm"
include "3eqtrrd.mm"
include "3eqtrd.mm"
include "mpteq2dva.mm"
include "dchrvmasumiflem1.mm"
include "eqeltrrd.mm"
include "o1dif.mm"
include "mpbird.mm"
include "vmacl.mm"
include "nndivre.mm"
include "mpancom.mm"
include "relogcl.mm"
include "sylancl.mm"
include "addcld.mm"
include "cle.mm"
include "cabs.mm"
include "abscld.mm"
include "adantrr.mm"
include "simprl.mm"
include "simprr.mm"
include "dchrvmasum2if.mm"
include "fveq2d.mm"
include "eqle.mm"
include "syl2anc.mm"
include "o1le.mm"

theorem dchrvmasumiflem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let c.1: class .1.
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cK: class K
  let cL: class L
  let cN: class N
  let cX: class X
  let cZ: class Z
  let va: setvar a
  let vm: setvar m
  let vk: setvar k
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z
  let vc: setvar c
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vp: setvar p
  let vt: setvar t
  let vd: setvar d
  let ve: setvar e
  let vr: setvar r
  let cI: class I
  let cJ: class J
  let vb: setvar b
  let vq: setvar q
  let vv: setvar v
  let cA: class A
  let cP: class P
  let wps: wff ps
  let cR: class R
  let cU: class U
  let cB: class B
  let cW: class W
  let cM: class M
  assume rpvmasum.z: |- Z = ( Z/nZ ` N )
  assume rpvmasum.l: |- L = ( ZRHom ` Z )
  assume rpvmasum.a: |- ( ph -> N e. NN )
  assume rpvmasum.g: |- G = ( DChr ` N )
  assume rpvmasum.d: |- D = ( Base ` G )
  assume rpvmasum.1: |- .1. = ( 0g ` G )
  assume dchrisum.b: |- ( ph -> X e. D )
  assume dchrisum.n1: |- ( ph -> X =/= .1. )
  assume dchrvmasumif.f: |- F = ( a e. NN |-> ( ( X ` ( L ` a ) ) / a ) )
  assume dchrvmasumif.c: |- ( ph -> C e. ( 0 [,) +oo ) )
  assume dchrvmasumif.s: |- ( ph -> seq 1 ( + , F ) ~~> S )
  assume dchrvmasumif.1: |- ( ph -> A. y e. ( 1 [,) +oo ) ( abs ` ( ( seq 1 ( + , F ) ` ( |_ ` y ) ) - S ) ) <_ ( C / y ) )
  assume dchrvmasumif.g: |- K = ( a e. NN |-> ( ( X ` ( L ` a ) ) x. ( ( log ` a ) / a ) ) )
  assume dchrvmasumif.e: |- ( ph -> E e. ( 0 [,) +oo ) )
  assume dchrvmasumif.t: |- ( ph -> seq 1 ( + , K ) ~~> T )
  assume dchrvmasumif.2: |- ( ph -> A. y e. ( 3 [,) +oo ) ( abs ` ( ( seq 1 ( + , K ) ` ( |_ ` y ) ) - T ) ) <_ ( E x. ( ( log ` y ) / y ) ) )

  disjoint n x
  disjoint n y
  disjoint x y
  disjoint .1. n
  disjoint .1. x
  disjoint .1. y
  disjoint C n
  disjoint C x
  disjoint C y
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint a x
  disjoint a y
  disjoint E x
  disjoint E y
  disjoint K y
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint n ph
  disjoint ph x
  disjoint T n
  disjoint T x
  disjoint T y
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint Z n
  disjoint Z x
  disjoint Z y
  disjoint D n
  disjoint D x
  disjoint D y
  disjoint a n
  disjoint L a
  disjoint L n
  disjoint L x
  disjoint L y
  disjoint X a
  disjoint X n
  disjoint X x
  disjoint X y
  disjoint F m
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m u
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n u
  disjoint n w
  disjoint n z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint c f
  disjoint c i
  disjoint c j
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c p
  disjoint c t
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint .1. c
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f p
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint .1. f
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i p
  disjoint i t
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint .1. i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j p
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint .1. j
  disjoint k p
  disjoint k t
  disjoint .1. k
  disjoint m p
  disjoint m t
  disjoint .1. m
  disjoint n p
  disjoint n t
  disjoint p t
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint .1. p
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint .1. t
  disjoint .1. z
  disjoint d m
  disjoint d n
  disjoint d x
  disjoint d y
  disjoint C d
  disjoint C m
  disjoint c d
  disjoint c e
  disjoint c r
  disjoint c u
  disjoint F c
  disjoint d e
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d p
  disjoint d r
  disjoint d t
  disjoint d u
  disjoint d z
  disjoint F d
  disjoint e i
  disjoint e j
  disjoint e k
  disjoint e n
  disjoint e p
  disjoint e r
  disjoint e t
  disjoint e u
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint F e
  disjoint i r
  disjoint i u
  disjoint F i
  disjoint j r
  disjoint j u
  disjoint F j
  disjoint k r
  disjoint F k
  disjoint n r
  disjoint p r
  disjoint p u
  disjoint F p
  disjoint r t
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint t u
  disjoint F t
  disjoint F u
  disjoint F z
  disjoint I i
  disjoint I k
  disjoint I n
  disjoint I u
  disjoint I x
  disjoint I z
  disjoint J i
  disjoint J k
  disjoint J n
  disjoint J u
  disjoint J x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a p
  disjoint a q
  disjoint a t
  disjoint a v
  disjoint a z
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint b m
  disjoint b p
  disjoint b q
  disjoint b t
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint c q
  disjoint c v
  disjoint A c
  disjoint d f
  disjoint d q
  disjoint d v
  disjoint A d
  disjoint f q
  disjoint f v
  disjoint A f
  disjoint i q
  disjoint i v
  disjoint A i
  disjoint j q
  disjoint j v
  disjoint A j
  disjoint k q
  disjoint k v
  disjoint A k
  disjoint m q
  disjoint m v
  disjoint A m
  disjoint p q
  disjoint p v
  disjoint A p
  disjoint q t
  disjoint q v
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint A q
  disjoint t v
  disjoint A t
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint E d
  disjoint E m
  disjoint K k
  disjoint m r
  disjoint K m
  disjoint K r
  disjoint G f
  disjoint N c
  disjoint f r
  disjoint f u
  disjoint N f
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint N m
  disjoint n q
  disjoint N p
  disjoint q r
  disjoint q u
  disjoint N q
  disjoint N r
  disjoint N t
  disjoint N u
  disjoint N z
  disjoint b n
  disjoint P b
  disjoint P i
  disjoint P k
  disjoint P m
  disjoint n v
  disjoint P n
  disjoint P q
  disjoint P v
  disjoint P x
  disjoint P y
  disjoint c ph
  disjoint d ph
  disjoint e f
  disjoint e m
  disjoint e ph
  disjoint f ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint p ph
  disjoint ph r
  disjoint ph t
  disjoint ph u
  disjoint ph z
  disjoint d ps
  disjoint m ps
  disjoint T d
  disjoint T m
  disjoint T p
  disjoint T r
  disjoint R c
  disjoint R d
  disjoint R i
  disjoint R k
  disjoint R m
  disjoint R n
  disjoint R u
  disjoint R x
  disjoint R z
  disjoint S c
  disjoint S d
  disjoint S k
  disjoint S m
  disjoint S r
  disjoint S t
  disjoint U k
  disjoint U m
  disjoint U n
  disjoint U p
  disjoint U u
  disjoint U x
  disjoint U z
  disjoint b r
  disjoint B b
  disjoint B c
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B m
  disjoint B n
  disjoint B q
  disjoint r v
  disjoint B r
  disjoint B v
  disjoint B y
  disjoint B z
  disjoint W c
  disjoint W f
  disjoint W t
  disjoint W x
  disjoint W z
  disjoint Z f
  disjoint Z k
  disjoint Z m
  disjoint Z p
  disjoint Z z
  disjoint D c
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D k
  disjoint D m
  disjoint D t
  disjoint D z
  disjoint a r
  disjoint a u
  disjoint b u
  disjoint L b
  disjoint L c
  disjoint L d
  disjoint L f
  disjoint L i
  disjoint L j
  disjoint L k
  disjoint L m
  disjoint L p
  disjoint L r
  disjoint L t
  disjoint u v
  disjoint L u
  disjoint L v
  disjoint L z
  disjoint M c
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint M m
  disjoint M n
  disjoint M r
  disjoint M u
  disjoint M x
  disjoint M z
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X m
  disjoint X r
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X z
  assert |- ( ph -> ( x e. RR+ |-> ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( X ` ( L ` n ) ) x. ( ( Lam ` n ) / n ) ) + if ( S = 0 , ( log ` x ) , 0 ) ) ) e. O(1) )

  proof
    wph
    vx
    crp
    c1
    vx
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vd
    cv
    #
    cL
    cfv
    cX
    cfv
    #
    @3
    cmu
    cfv
    #
    @3
    cdiv
    co
    #
    cmul
    co
    #
    c1
    @0
    @3
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vk
    cv
    #
    cL
    cfv
    cX
    cfv
    #
    cS
    cc0
    wceq
    #
    @8
    @11
    cif
    #
    clog
    cfv
    #
    @11
    cdiv
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmul
    co
    #
    vd
    csu
    #
    @2
    vn
    cv
    #
    cL
    cfv
    cX
    cfv
    #
    @21
    cvma
    cfv
    #
    @21
    cdiv
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    @13
    @0
    clog
    cfv
    #
    cc0
    cif
    #
    caddc
    co
    #
    c1
    cc
    wph
    1red
    wph
    vx
    crp
    @20
    cmpt
    co1
    wcel
    vx
    crp
    @2
    @7
    vd
    csu
    #
    cS
    cmul
    co
    #
    @13
    cc0
    cT
    cS
    cdiv
    co
    #
    cif
    #
    cmul
    co
    #
    cmpt
    co1
    wcel
    wph
    vx
    crp
    @31
    @33
    cc
    wph
    @0
    crp
    wcel
    #
    wa
    #
    @30
    cS
    @36
    @2
    @7
    vd
    @36
    c1
    @1
    fzfid
    #
    @36
    @3
    @2
    wcel
    #
    wa
    #
    @4
    @6
    @39
    @3
    cD
    cG
    cL
    cN
    cX
    cZ
    rpvmasum.g
    rpvmasum.z
    rpvmasum.d
    rpvmasum.l
    wph
    cX
    cD
    wcel
    #
    @35
    @38
    dchrisum.b
    ad2antrr
    #
    @38
    @3
    cz
    wcel
    @36
    @3
    c1
    @1
    elfzelz
    adantl
    dchrzrhcl
    @39
    @6
    @39
    @5
    @3
    @39
    @5
    @39
    @3
    cn
    wcel
    #
    @5
    cz
    wcel
    @38
    @42
    @36
    @3
    @1
    elfznn
    #
    adantl
    #
    @3
    mucl
    syl
    zred
    @44
    nndivred
    recnd
    mulcld
    #
    fsumcl
    #
    wph
    cS
    cc
    wcel
    #
    @35
    wph
    caddc
    cF
    c1
    cseq
    #
    cS
    cli
    wbr
    @47
    dchrvmasumif.s
    cS
    @48
    climcl
    syl
    #
    adantr
    #
    mulcld
    #
    wph
    @33
    cc
    wcel
    #
    @35
    wph
    @13
    cc0
    @32
    cc
    wph
    @13
    wa
    0cnd
    @13
    wn
    #
    wph
    cS
    cc0
    wne
    #
    @32
    cc
    wcel
    cS
    cc0
    df-ne
    #
    wph
    @54
    wa
    #
    cT
    cS
    wph
    cT
    cc
    wcel
    #
    @54
    wph
    caddc
    cK
    c1
    cseq
    #
    cT
    cli
    wbr
    @57
    dchrvmasumif.t
    cT
    @58
    climcl
    syl
    #
    adantr
    #
    wph
    @47
    @54
    @49
    adantr
    #
    wph
    @54
    simpr
    #
    divcld
    sylan2br
    ifclda
    #
    adantr
    #
    wph
    vx
    vy
    cC
    cD
    cS
    c.1
    cF
    cG
    cL
    cN
    cX
    cZ
    va
    vd
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    rpvmasum.g
    rpvmasum.d
    rpvmasum.1
    dchrisum.b
    dchrisum.n1
    dchrvmasumif.f
    dchrvmasumif.c
    dchrvmasumif.s
    dchrvmasumif.1
    dchrmusum2
    wph
    crp
    cr
    wss
    @52
    vx
    crp
    @33
    cmpt
    co1
    wcel
    rpssre
    @63
    vx
    crp
    @33
    o1const
    sylancr
    o1mul2
    wph
    vx
    crp
    @20
    @34
    @36
    @2
    @19
    vd
    @37
    @39
    @7
    @18
    @45
    @39
    @10
    @17
    vk
    @39
    c1
    @9
    fzfid
    @39
    @11
    @10
    wcel
    #
    wa
    #
    @12
    @16
    @66
    @11
    cD
    cG
    cL
    cN
    cX
    cZ
    rpvmasum.g
    rpvmasum.z
    rpvmasum.d
    rpvmasum.l
    @39
    @40
    @65
    @41
    adantr
    @65
    @11
    cz
    wcel
    @39
    @11
    c1
    @9
    elfzelz
    adantl
    dchrzrhcl
    @66
    @16
    @66
    @15
    @11
    @66
    @14
    @39
    @8
    crp
    wcel
    #
    @11
    crp
    wcel
    @14
    crp
    wcel
    @65
    @36
    @35
    @3
    crp
    wcel
    @67
    @38
    wph
    @35
    simpr
    @38
    @3
    @43
    nnrpd
    @0
    @3
    rpdivcl
    syl2an
    @65
    @11
    @11
    @9
    elfznn
    #
    nnrpd
    @13
    @8
    @11
    crp
    ifcl
    syl2an
    relogcld
    @65
    @11
    cn
    wcel
    @39
    @68
    adantl
    nndivred
    recnd
    mulcld
    fsumcl
    #
    mulcld
    #
    fsumcl
    #
    @36
    @31
    @33
    @51
    @64
    mulcld
    wph
    vx
    crp
    @2
    @7
    @18
    @13
    cc0
    cT
    cif
    #
    cmin
    co
    cmul
    co
    #
    vd
    csu
    #
    cmpt
    vx
    crp
    @20
    @34
    cmin
    co
    #
    cmpt
    co1
    wph
    vx
    crp
    @74
    @75
    @36
    @74
    @2
    @19
    @7
    @72
    cmul
    co
    #
    cmin
    co
    #
    vd
    csu
    @20
    @2
    @76
    vd
    csu
    #
    cmin
    co
    @75
    @36
    @2
    @73
    @77
    vd
    @39
    @7
    @18
    @72
    @45
    @69
    @39
    cc0
    cc
    wcel
    #
    @57
    @72
    cc
    wcel
    #
    0cn
    wph
    @57
    @35
    @38
    @59
    ad2antrr
    @13
    cc0
    cT
    cc
    ifcl
    #
    sylancr
    #
    subdid
    sumeq2dv
    @36
    @2
    @19
    @76
    vd
    @37
    @70
    @39
    @7
    @72
    @45
    @82
    mulcld
    fsumsub
    @36
    @78
    @34
    @20
    cmin
    @36
    @34
    @30
    cS
    @33
    cmul
    co
    #
    cmul
    co
    @30
    @72
    cmul
    co
    @78
    @36
    @30
    cS
    @33
    @46
    @50
    @64
    mulassd
    @36
    @83
    @72
    @30
    cmul
    wph
    @83
    @72
    wceq
    @35
    wph
    @83
    @13
    cS
    cc0
    cmul
    co
    #
    cS
    @32
    cmul
    co
    #
    cif
    #
    @72
    @13
    cS
    cc0
    @32
    cmul
    ovif2
    wph
    @86
    @13
    cc0
    @85
    cif
    @72
    wph
    @13
    @84
    cc0
    @85
    wph
    cS
    @49
    mul01d
    ifeq1d
    wph
    @13
    @85
    cT
    cc0
    @53
    wph
    @54
    @85
    cT
    wceq
    @55
    @56
    cT
    cS
    @60
    @61
    @62
    divcan2d
    sylan2br
    ifeq2da
    eqtrd
    syl5eq
    adantr
    oveq2d
    @36
    @2
    @7
    @72
    vd
    @37
    wph
    @80
    @35
    wph
    @79
    @57
    @80
    0cn
    @59
    @81
    sylancr
    adantr
    @45
    fsummulc1
    3eqtrrd
    oveq2d
    3eqtrd
    mpteq2dva
    wph
    vx
    vy
    cC
    cD
    cS
    cT
    c.1
    vk
    cE
    cF
    cG
    cK
    cL
    cN
    cX
    cZ
    va
    vd
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    rpvmasum.g
    rpvmasum.d
    rpvmasum.1
    dchrisum.b
    dchrisum.n1
    dchrvmasumif.f
    dchrvmasumif.c
    dchrvmasumif.s
    dchrvmasumif.1
    dchrvmasumif.g
    dchrvmasumif.e
    dchrvmasumif.t
    dchrvmasumif.2
    dchrvmasumiflem1
    eqeltrrd
    o1dif
    mpbird
    @71
    @36
    @26
    @28
    @36
    @2
    @25
    vn
    @37
    @36
    @21
    @2
    wcel
    #
    wa
    #
    @22
    @24
    @88
    @21
    cD
    cG
    cL
    cN
    cX
    cZ
    rpvmasum.g
    rpvmasum.z
    rpvmasum.d
    rpvmasum.l
    wph
    @40
    @35
    @87
    dchrisum.b
    ad2antrr
    @87
    @21
    cz
    wcel
    @36
    @21
    c1
    @1
    elfzelz
    adantl
    dchrzrhcl
    @88
    @24
    @88
    @21
    cn
    wcel
    #
    @24
    cr
    wcel
    #
    @87
    @89
    @36
    @21
    @1
    elfznn
    adantl
    @23
    cr
    wcel
    @89
    @90
    @21
    vmacl
    @23
    @21
    nndivre
    mpancom
    syl
    recnd
    mulcld
    fsumcl
    @36
    @27
    cc
    wcel
    @79
    @28
    cc
    wcel
    @36
    @27
    @35
    @27
    cr
    wcel
    wph
    @0
    relogcl
    adantl
    recnd
    0cn
    @13
    @27
    cc0
    cc
    ifcl
    sylancl
    addcld
    #
    wph
    @35
    c1
    @0
    cle
    wbr
    #
    wa
    #
    wa
    #
    @29
    cabs
    cfv
    #
    cr
    wcel
    #
    @95
    @20
    cabs
    cfv
    #
    wceq
    @95
    @97
    cle
    wbr
    wph
    @35
    @96
    @92
    @36
    @29
    @91
    abscld
    adantrr
    @94
    @29
    @20
    cabs
    @94
    @13
    @0
    cD
    c.1
    vk
    vn
    cG
    cL
    cN
    cX
    cZ
    vd
    rpvmasum.z
    rpvmasum.l
    wph
    cN
    cn
    wcel
    @93
    rpvmasum.a
    adantr
    rpvmasum.g
    rpvmasum.d
    rpvmasum.1
    wph
    @40
    @93
    dchrisum.b
    adantr
    wph
    cX
    c.1
    wne
    @93
    dchrisum.n1
    adantr
    wph
    @35
    @92
    simprl
    wph
    @35
    @92
    simprr
    dchrvmasum2if
    fveq2d
    @95
    @97
    eqle
    syl2anc
    o1le
end
