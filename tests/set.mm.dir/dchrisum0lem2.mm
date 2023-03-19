include "crp.mm"
include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "csqrt.mm"
include "csu.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "cmul.mm"
include "cc.mm"
include "wa.mm"
include "2cnd.mm"
include "rpcn.mm"
include "adantl.mm"
include "fzfid.mm"
include "csn.mm"
include "cdif.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "eldifad.mm"
include "ad2antrr.mm"
include "cz.mm"
include "elfzelz.mm"
include "dchrzrhcl.mm"
include "elfznn.mm"
include "nnrpd.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divcld.mm"
include "fsumcl.mm"
include "mulcld.mm"
include "cr.mm"
include "wss.mm"
include "rpssre.mm"
include "2cn.mm"
include "o1const.mm"
include "mp2an.mm"
include "a1i.mm"
include "1red.mm"
include "cpnf.mm"
include "cico.mm"
include "cle.mm"
include "wbr.mm"
include "elrege0.mm"
include "simplbi.mm"
include "syl.mm"
include "cabs.mm"
include "absmuld.mm"
include "rprege0.mm"
include "absid.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "adantrr.mm"
include "caddc.mm"
include "cseq.mm"
include "cmin.mm"
include "subid1d.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "id.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt3i.mm"
include "adantlrr.mm"
include "cuz.mm"
include "clt.mm"
include "rpregt0.mm"
include "ad2antrl.mm"
include "simpld.mm"
include "simprr.mm"
include "flge1nn.mm"
include "syl2anc.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "fsumser.mm"
include "wne.mm"
include "eldifsni.mm"
include "dchrvmaeq0.mm"
include "mpbid.mm"
include "adantr.mm"
include "eqcomd.mm"
include "eqtr3d.mm"
include "wral.mm"
include "wb.mm"
include "1re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "sylanbrc.mm"
include "oveq2.mm"
include "breq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqbrtrd.mm"
include "abscld.mm"
include "lemuldiv2.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "elo1d.mm"
include "o1mul2.mm"
include "rpsqrtcld.mm"
include "mulcl.mm"
include "sylancr.mm"
include "2re.mm"
include "simpr.mm"
include "2z.mm"
include "rpexpcl.mm"
include "sylancl.mm"
include "rpdivcl.mm"
include "syl2an.mm"
include "rpred.mm"
include "remulcl.mm"
include "recnd.mm"
include "fsumsub.mm"
include "rpcnne0d.mm"
include "reccl.mm"
include "subdid.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "divrecd.mm"
include "sumeq2dv.mm"
include "fsummulc2.mm"
include "eqtr4d.mm"
include "3eqtr4d.mm"
include "mulassd.mm"
include "div12d.mm"
include "divdiv1.mm"
include "rprege0d.mm"
include "remsqsqrt.mm"
include "eqtr2d.mm"
include "sqrtdiv.mm"
include "ad2antlr.mm"
include "sqrtsq.mm"
include "divass.mm"
include "3eqtr3d.mm"
include "mpteq2dva.mm"
include "dchrisum0lem2a.mm"
include "eqeltrrd.mm"
include "o1dif.mm"

theorem dchrisum0lem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let c.1: class .1.
  let vm: setvar m
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let cN: class N
  let cW: class W
  let cX: class X
  let cZ: class Z
  let va: setvar a
  let vd: setvar d
  let vk: setvar k
  let vn: setvar n
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z
  let vc: setvar c
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vp: setvar p
  let vt: setvar t
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
  let cB: class B
  let cM: class M
  assume rpvmasum.z: |- Z = ( Z/nZ ` N )
  assume rpvmasum.l: |- L = ( ZRHom ` Z )
  assume rpvmasum.a: |- ( ph -> N e. NN )
  assume rpvmasum2.g: |- G = ( DChr ` N )
  assume rpvmasum2.d: |- D = ( Base ` G )
  assume rpvmasum2.1: |- .1. = ( 0g ` G )
  assume rpvmasum2.w: |- W = { y e. ( D \ { .1. } ) | sum_ m e. NN ( ( y ` ( L ` m ) ) / m ) = 0 }
  assume dchrisum0.b: |- ( ph -> X e. W )
  assume dchrisum0lem1.f: |- F = ( a e. NN |-> ( ( X ` ( L ` a ) ) / ( sqrt ` a ) ) )
  assume dchrisum0.c: |- ( ph -> C e. ( 0 [,) +oo ) )
  assume dchrisum0.s: |- ( ph -> seq 1 ( + , F ) ~~> S )
  assume dchrisum0.1: |- ( ph -> A. y e. ( 1 [,) +oo ) ( abs ` ( ( seq 1 ( + , F ) ` ( |_ ` y ) ) - S ) ) <_ ( C / ( sqrt ` y ) ) )
  assume dchrisum0lem2.h: |- H = ( y e. RR+ |-> ( sum_ d e. ( 1 ... ( |_ ` y ) ) ( 1 / ( sqrt ` d ) ) - ( 2 x. ( sqrt ` y ) ) ) )
  assume dchrisum0lem2.u: |- ( ph -> H ~~>r U )
  assume dchrisum0lem2.k: |- K = ( a e. NN |-> ( ( X ` ( L ` a ) ) / a ) )
  assume dchrisum0lem2.e: |- ( ph -> E e. ( 0 [,) +oo ) )
  assume dchrisum0lem2.t: |- ( ph -> seq 1 ( + , K ) ~~> T )
  assume dchrisum0lem2.3: |- ( ph -> A. y e. ( 1 [,) +oo ) ( abs ` ( ( seq 1 ( + , K ) ` ( |_ ` y ) ) - T ) ) <_ ( E / y ) )

  disjoint F m
  disjoint m x
  disjoint m y
  disjoint x y
  disjoint .1. m
  disjoint .1. x
  disjoint .1. y
  disjoint d m
  disjoint d x
  disjoint d y
  disjoint C d
  disjoint C m
  disjoint C x
  disjoint C y
  disjoint F d
  disjoint F x
  disjoint F y
  disjoint a d
  disjoint a m
  disjoint a x
  disjoint a y
  disjoint E d
  disjoint E m
  disjoint E x
  disjoint E y
  disjoint K m
  disjoint K y
  disjoint N m
  disjoint N x
  disjoint N y
  disjoint d ph
  disjoint m ph
  disjoint ph x
  disjoint T d
  disjoint T m
  disjoint T x
  disjoint T y
  disjoint S d
  disjoint S m
  disjoint S x
  disjoint S y
  disjoint U m
  disjoint U x
  disjoint W x
  disjoint Z m
  disjoint Z x
  disjoint Z y
  disjoint D m
  disjoint D x
  disjoint D y
  disjoint L a
  disjoint L d
  disjoint L m
  disjoint L x
  disjoint L y
  disjoint X a
  disjoint X d
  disjoint X m
  disjoint X x
  disjoint X y
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
  disjoint m z
  disjoint n u
  disjoint n w
  disjoint n x
  disjoint n y
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
  disjoint n p
  disjoint n t
  disjoint .1. n
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
  disjoint d n
  disjoint C n
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
  disjoint F n
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
  disjoint a f
  disjoint a i
  disjoint a j
  disjoint a k
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
  disjoint K k
  disjoint m r
  disjoint K r
  disjoint G f
  disjoint N c
  disjoint f r
  disjoint f u
  disjoint N f
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint n q
  disjoint N n
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
  disjoint e f
  disjoint e m
  disjoint e ph
  disjoint f ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint p ph
  disjoint ph r
  disjoint ph t
  disjoint ph u
  disjoint ph z
  disjoint d ps
  disjoint m ps
  disjoint T n
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
  disjoint S k
  disjoint S n
  disjoint S r
  disjoint S t
  disjoint U k
  disjoint U n
  disjoint U p
  disjoint U u
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
  disjoint W z
  disjoint Z f
  disjoint Z k
  disjoint Z n
  disjoint Z p
  disjoint Z z
  disjoint D c
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D k
  disjoint D n
  disjoint D t
  disjoint D z
  disjoint a n
  disjoint a r
  disjoint a u
  disjoint b u
  disjoint L b
  disjoint L c
  disjoint L f
  disjoint L i
  disjoint L j
  disjoint L k
  disjoint L n
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
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X n
  disjoint X r
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X z
  assert |- ( ph -> ( x e. RR+ |-> sum_ m e. ( 1 ... ( |_ ` x ) ) sum_ d e. ( 1 ... ( |_ ` ( ( x ^ 2 ) / m ) ) ) ( ( ( X ` ( L ` m ) ) / ( sqrt ` m ) ) / ( sqrt ` d ) ) ) e. O(1) )

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
    c1
    @0
    c2
    cexp
    co
    #
    vm
    cv
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
    @4
    cL
    cfv
    #
    cX
    cfv
    #
    @4
    csqrt
    cfv
    #
    cdiv
    co
    #
    vd
    cv
    #
    csqrt
    cfv
    #
    cdiv
    co
    #
    vd
    csu
    #
    vm
    csu
    #
    cmpt
    co1
    wcel
    vx
    crp
    c2
    @0
    @2
    @9
    @4
    cdiv
    co
    #
    vm
    csu
    #
    cmul
    co
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
    c2
    @19
    cc
    wph
    @0
    crp
    wcel
    #
    wa
    #
    2cnd
    #
    @22
    @0
    @18
    @21
    @0
    cc
    wcel
    #
    wph
    @0
    rpcn
    adantl
    #
    @22
    @2
    @17
    vm
    @22
    c1
    @1
    fzfid
    #
    @22
    @4
    @2
    wcel
    #
    wa
    #
    @9
    @4
    @28
    @4
    cD
    cG
    cL
    cN
    cX
    cZ
    rpvmasum2.g
    rpvmasum.z
    rpvmasum2.d
    rpvmasum.l
    wph
    cX
    cD
    wcel
    @21
    @27
    wph
    cX
    cD
    c.1
    csn
    #
    wph
    cW
    cD
    @29
    cdif
    #
    cX
    cW
    cn
    @8
    vy
    cv
    #
    cfv
    @4
    cdiv
    co
    vm
    csu
    cc0
    wceq
    #
    vy
    @30
    crab
    @30
    rpvmasum2.w
    @32
    vy
    @30
    ssrab2
    eqsstri
    dchrisum0.b
    sseldi
    #
    eldifad
    #
    ad2antrr
    @27
    @4
    cz
    wcel
    @22
    @4
    c1
    @1
    elfzelz
    adantl
    dchrzrhcl
    #
    @28
    @4
    @27
    @4
    crp
    wcel
    #
    @22
    @27
    @4
    @4
    @1
    elfznn
    #
    nnrpd
    #
    adantl
    #
    rpcnd
    @28
    @4
    @39
    rpne0d
    divcld
    #
    fsumcl
    #
    mulcld
    #
    vx
    crp
    c2
    cmpt
    co1
    wcel
    #
    wph
    crp
    cr
    wss
    #
    c2
    cc
    wcel
    #
    @43
    rpssre
    2cn
    vx
    crp
    c2
    o1const
    mp2an
    a1i
    wph
    vx
    crp
    @19
    c1
    cE
    @44
    wph
    rpssre
    a1i
    @42
    wph
    1red
    wph
    cE
    cc0
    cpnf
    cico
    co
    wcel
    #
    cE
    cr
    wcel
    #
    dchrisum0lem2.e
    @46
    @47
    cc0
    cE
    cle
    wbr
    cE
    elrege0
    simplbi
    syl
    #
    wph
    @21
    c1
    @0
    cle
    wbr
    #
    wa
    #
    wa
    #
    @19
    cabs
    cfv
    #
    @0
    @18
    cabs
    cfv
    #
    cmul
    co
    #
    cE
    cle
    wph
    @21
    @52
    @54
    wceq
    @49
    @22
    @52
    @0
    cabs
    cfv
    #
    @53
    cmul
    co
    @54
    @22
    @0
    @18
    @25
    @41
    absmuld
    @22
    @55
    @0
    @53
    cmul
    @22
    @0
    cr
    wcel
    #
    cc0
    @0
    cle
    wbr
    wa
    #
    @55
    @0
    wceq
    @21
    @57
    wph
    @0
    rprege0
    #
    adantl
    @0
    absid
    syl
    oveq1d
    eqtrd
    adantrr
    @51
    @54
    cE
    cle
    wbr
    #
    @53
    cE
    @0
    cdiv
    co
    #
    cle
    wbr
    #
    @51
    @53
    @1
    caddc
    cK
    c1
    cseq
    #
    cfv
    #
    cT
    cmin
    co
    #
    cabs
    cfv
    #
    @60
    cle
    @51
    @18
    @64
    cabs
    @51
    @18
    cc0
    cmin
    co
    @18
    @64
    @51
    @18
    wph
    @21
    @18
    cc
    wcel
    @49
    @41
    adantrr
    #
    subid1d
    @51
    @18
    @63
    cc0
    cT
    cmin
    @51
    @17
    vm
    cK
    c1
    @1
    wph
    @21
    @27
    @4
    cK
    cfv
    @17
    wceq
    #
    @49
    @28
    @4
    cn
    wcel
    #
    @67
    @27
    @68
    @22
    @37
    adantl
    va
    @4
    va
    cv
    #
    cL
    cfv
    #
    cX
    cfv
    #
    @69
    cdiv
    co
    @17
    cn
    cK
    va
    vm
    weq
    #
    @71
    @9
    @69
    @4
    cdiv
    @72
    @70
    @8
    cX
    @69
    @4
    cL
    fveq2
    fveq2d
    @72
    id
    oveq12d
    dchrisum0lem2.k
    @71
    @69
    cdiv
    ovex
    fvmpt3i
    syl
    adantlrr
    @51
    @1
    cn
    c1
    cuz
    cfv
    @51
    @56
    @49
    @1
    cn
    wcel
    @51
    @56
    cc0
    @0
    clt
    wbr
    #
    @21
    @56
    @73
    wa
    #
    wph
    @49
    @0
    rpregt0
    ad2antrl
    #
    simpld
    #
    wph
    @21
    @49
    simprr
    #
    @0
    flge1nn
    syl2anc
    nnuz
    syl6eleq
    wph
    @21
    @27
    @17
    cc
    wcel
    @49
    @40
    adantlrr
    fsumser
    @51
    cT
    cc0
    wph
    cT
    cc0
    wceq
    #
    @50
    wph
    cX
    cW
    wcel
    @78
    dchrisum0.b
    wph
    vy
    cE
    cD
    cT
    c.1
    vm
    cK
    cG
    cL
    cN
    cW
    cX
    cZ
    va
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    rpvmasum2.g
    rpvmasum2.d
    rpvmasum2.1
    @34
    wph
    cX
    @30
    wcel
    cX
    c.1
    wne
    @33
    cX
    cD
    c.1
    eldifsni
    syl
    dchrisum0lem2.k
    dchrisum0lem2.e
    dchrisum0lem2.t
    dchrisum0lem2.3
    rpvmasum2.w
    dchrvmaeq0
    mpbid
    adantr
    eqcomd
    oveq12d
    eqtr3d
    fveq2d
    @51
    @0
    c1
    cpnf
    cico
    co
    #
    wcel
    #
    @31
    cfl
    cfv
    #
    @62
    cfv
    #
    cT
    cmin
    co
    #
    cabs
    cfv
    #
    cE
    @31
    cdiv
    co
    #
    cle
    wbr
    #
    vy
    @79
    wral
    #
    @65
    @60
    cle
    wbr
    #
    @51
    @56
    @49
    @80
    @76
    @77
    c1
    cr
    wcel
    @80
    @56
    @49
    wa
    wb
    1re
    c1
    @0
    elicopnf
    ax-mp
    sylanbrc
    wph
    @87
    @50
    dchrisum0lem2.3
    adantr
    @86
    @88
    vy
    @0
    @79
    vy
    vx
    weq
    #
    @84
    @65
    @85
    @60
    cle
    @89
    @83
    @64
    cabs
    @89
    @82
    @63
    cT
    cmin
    @89
    @81
    @1
    @62
    @31
    @0
    cfl
    fveq2
    fveq2d
    oveq1d
    fveq2d
    @31
    @0
    cE
    cdiv
    oveq2
    breq12d
    rspcv
    sylc
    eqbrtrd
    @51
    @53
    cr
    wcel
    @47
    @74
    @59
    @61
    wb
    @51
    @18
    @66
    abscld
    wph
    @47
    @50
    @48
    adantr
    @75
    @53
    cE
    @0
    lemuldiv2
    syl3anc
    mpbird
    eqbrtrd
    elo1d
    o1mul2
    wph
    vx
    crp
    @16
    @20
    @22
    @2
    @15
    vm
    @26
    @28
    @7
    @14
    vd
    @28
    c1
    @6
    fzfid
    #
    @28
    @12
    @7
    wcel
    #
    wa
    #
    @11
    @13
    @28
    @11
    cc
    wcel
    @91
    @28
    @9
    @10
    @35
    @28
    @10
    @28
    @4
    @39
    rpsqrtcld
    #
    rpcnd
    #
    @28
    @10
    @93
    rpne0d
    #
    divcld
    #
    adantr
    #
    @92
    @13
    @92
    @12
    @92
    @12
    @91
    @12
    cn
    wcel
    @28
    @12
    @6
    elfznn
    adantl
    nnrpd
    rpsqrtcld
    #
    rpcnd
    #
    @92
    @13
    @98
    rpne0d
    #
    divcld
    fsumcl
    #
    fsumcl
    @22
    @45
    @19
    cc
    wcel
    @20
    cc
    wcel
    2cn
    @42
    c2
    @19
    mulcl
    sylancr
    wph
    vx
    crp
    @2
    @11
    @5
    cH
    cfv
    #
    cmul
    co
    #
    vm
    csu
    #
    cmpt
    vx
    crp
    @16
    @20
    cmin
    co
    #
    cmpt
    co1
    wph
    vx
    crp
    @104
    @105
    @22
    @2
    @15
    @11
    c2
    @5
    csqrt
    cfv
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
    vm
    csu
    @16
    @2
    @108
    vm
    csu
    #
    cmin
    co
    @104
    @105
    @22
    @2
    @15
    @108
    vm
    @26
    @101
    @28
    @11
    @107
    @96
    @28
    @107
    @28
    c2
    cr
    wcel
    @106
    cr
    wcel
    @107
    cr
    wcel
    2re
    @28
    @106
    @28
    @5
    @22
    @3
    crp
    wcel
    #
    @36
    @5
    crp
    wcel
    #
    @27
    @22
    @21
    c2
    cz
    wcel
    @111
    wph
    @21
    simpr
    2z
    @0
    c2
    rpexpcl
    sylancl
    #
    @38
    @3
    @4
    rpdivcl
    syl2an
    #
    rpsqrtcld
    rpred
    c2
    @106
    remulcl
    sylancr
    recnd
    #
    mulcld
    fsumsub
    @22
    @2
    @103
    @109
    vm
    @28
    @11
    @7
    c1
    @13
    cdiv
    co
    #
    vd
    csu
    #
    @107
    cmin
    co
    #
    cmul
    co
    @11
    @117
    cmul
    co
    #
    @108
    cmin
    co
    @103
    @109
    @28
    @11
    @117
    @107
    @96
    @28
    @7
    @116
    vd
    @90
    @92
    @13
    cc
    wcel
    @13
    cc0
    wne
    wa
    @116
    cc
    wcel
    @92
    @13
    @98
    rpcnne0d
    @13
    reccl
    syl
    #
    fsumcl
    @115
    subdid
    @28
    @102
    @118
    @11
    cmul
    @28
    @112
    @102
    @118
    wceq
    @114
    vy
    @5
    c1
    @81
    cfz
    co
    #
    @116
    vd
    csu
    #
    c2
    @31
    csqrt
    cfv
    #
    cmul
    co
    #
    cmin
    co
    @118
    crp
    cH
    @31
    @5
    wceq
    #
    @122
    @117
    @124
    @107
    cmin
    @125
    @121
    @7
    @116
    vd
    @125
    @81
    @6
    c1
    cfz
    @31
    @5
    cfl
    fveq2
    oveq2d
    sumeq1d
    @125
    @123
    @106
    c2
    cmul
    @31
    @5
    csqrt
    fveq2
    oveq2d
    oveq12d
    dchrisum0lem2.h
    @122
    @124
    cmin
    ovex
    fvmpt3i
    syl
    oveq2d
    @28
    @15
    @119
    @108
    cmin
    @28
    @15
    @7
    @11
    @116
    cmul
    co
    #
    vd
    csu
    @119
    @28
    @7
    @14
    @126
    vd
    @92
    @11
    @13
    @97
    @99
    @100
    divrecd
    sumeq2dv
    @28
    @7
    @116
    @11
    vd
    @90
    @96
    @120
    fsummulc2
    eqtr4d
    oveq1d
    3eqtr4d
    sumeq2dv
    @22
    @20
    @110
    @16
    cmin
    @22
    c2
    @0
    cmul
    co
    #
    @18
    cmul
    co
    @2
    @127
    @17
    cmul
    co
    #
    vm
    csu
    @20
    @110
    @22
    @2
    @17
    @127
    vm
    @26
    @22
    @45
    @24
    @127
    cc
    wcel
    #
    2cn
    @25
    c2
    @0
    mulcl
    sylancr
    #
    @40
    fsummulc2
    @22
    c2
    @0
    @18
    @23
    @25
    @41
    mulassd
    @22
    @2
    @128
    @108
    vm
    @28
    @127
    @11
    @10
    cdiv
    co
    #
    cmul
    co
    @11
    @127
    @10
    cdiv
    co
    #
    cmul
    co
    @128
    @108
    @28
    @127
    @11
    @10
    @22
    @129
    @27
    @130
    adantr
    @96
    @94
    @95
    div12d
    @28
    @17
    @131
    @127
    cmul
    @28
    @131
    @9
    @10
    @10
    cmul
    co
    #
    cdiv
    co
    #
    @17
    @28
    @9
    cc
    wcel
    @10
    cc
    wcel
    @10
    cc0
    wne
    wa
    #
    @135
    @131
    @134
    wceq
    @35
    @28
    @10
    @93
    rpcnne0d
    #
    @136
    @9
    @10
    @10
    divdiv1
    syl3anc
    @28
    @133
    @4
    @9
    cdiv
    @28
    @4
    cr
    wcel
    cc0
    @4
    cle
    wbr
    wa
    @133
    @4
    wceq
    @28
    @4
    @39
    rprege0d
    @4
    remsqsqrt
    syl
    oveq2d
    eqtr2d
    oveq2d
    @28
    @107
    @132
    @11
    cmul
    @28
    @107
    c2
    @0
    @10
    cdiv
    co
    #
    cmul
    co
    #
    @132
    @28
    @106
    @137
    c2
    cmul
    @28
    @106
    @3
    csqrt
    cfv
    #
    @10
    cdiv
    co
    #
    @137
    @28
    @3
    cr
    wcel
    cc0
    @3
    cle
    wbr
    wa
    @36
    @106
    @140
    wceq
    @28
    @3
    @22
    @111
    @27
    @113
    adantr
    rprege0d
    @39
    @3
    @4
    sqrtdiv
    syl2anc
    @28
    @139
    @0
    @10
    cdiv
    @28
    @57
    @139
    @0
    wceq
    @21
    @57
    wph
    @27
    @58
    ad2antlr
    @0
    sqrtsq
    syl
    oveq1d
    eqtrd
    oveq2d
    @28
    @45
    @24
    @135
    @132
    @138
    wceq
    @28
    2cnd
    @22
    @24
    @27
    @25
    adantr
    @136
    c2
    @0
    @10
    divass
    syl3anc
    eqtr4d
    oveq2d
    3eqtr4d
    sumeq2dv
    3eqtr3d
    oveq2d
    3eqtr4d
    mpteq2dva
    wph
    vx
    vy
    cC
    cD
    cS
    cU
    c.1
    vm
    cF
    cG
    cH
    cL
    cN
    cW
    cX
    cZ
    va
    vd
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    rpvmasum2.g
    rpvmasum2.d
    rpvmasum2.1
    rpvmasum2.w
    dchrisum0.b
    dchrisum0lem1.f
    dchrisum0.c
    dchrisum0.s
    dchrisum0.1
    dchrisum0lem2.h
    dchrisum0lem2.u
    dchrisum0lem2a
    eqeltrrd
    o1dif
    mpbird
end
