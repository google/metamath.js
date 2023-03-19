include "cv.mm"
include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "caddc.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "csqrt.mm"
include "csu.mm"
include "cabs.mm"
include "cseq.mm"
include "cmin.mm"
include "cmul.mm"
include "fzfid.mm"
include "cc.mm"
include "cun.mm"
include "ssun2.mm"
include "cuz.mm"
include "wceq.mm"
include "cn.mm"
include "cn0.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "simpr.mm"
include "rprege0d.mm"
include "flge0nn0.mm"
include "syl.mm"
include "nn0p1nn.mm"
include "adantr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "dchrisum0lem1a.mm"
include "simprd.mm"
include "fzsplit2.mm"
include "syl2anc.mm"
include "syl5sseqr.mm"
include "sselda.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "eldifad.mm"
include "ad3antrrr.mm"
include "cz.mm"
include "elfzelz.mm"
include "adantl.mm"
include "dchrzrhcl.mm"
include "elfznn.mm"
include "nnrpd.mm"
include "rpsqrtcld.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divcld.mm"
include "syldan.mm"
include "fsumcl.mm"
include "abscld.mm"
include "wf.mm"
include "1zzd.mm"
include "nnz.mm"
include "nnrp.mm"
include "cmpt.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "serf.mm"
include "ad2antrr.mm"
include "clt.mm"
include "rpregt0d.mm"
include "simpld.mm"
include "1red.mm"
include "nnred.mm"
include "nnge1d.mm"
include "wb.mm"
include "rpred.mm"
include "fznnfl.mm"
include "simplbda.mm"
include "letrd.mm"
include "flge1nn.mm"
include "eluznn.mm"
include "ffvelrnd.mm"
include "cli.mm"
include "climcl.mm"
include "subcld.mm"
include "readdcld.mm"
include "2re.mm"
include "cpnf.mm"
include "cico.mm"
include "elrege0.mm"
include "sylib.mm"
include "remulcl.mm"
include "sylancr.mm"
include "rerpdivcld.mm"
include "ssun1.mm"
include "ovex.mm"
include "fvmpt3i.mm"
include "fsumser.mm"
include "eqeltrd.mm"
include "pncan2d.mm"
include "cin.mm"
include "c0.mm"
include "reflcl.mm"
include "ltp1d.mm"
include "fzdisj.mm"
include "fsumsplit.mm"
include "eqtr3d.mm"
include "abs3difd.mm"
include "eqbrtrd.mm"
include "simplr.mm"
include "2z.mm"
include "rpexpcl.mm"
include "sylancl.mm"
include "rpdivcld.mm"
include "wral.mm"
include "nndivre.mm"
include "syl2an.mm"
include "1re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "sylanbrc.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "sqrtle.mm"
include "mpbid.mm"
include "lediv2a.mm"
include "syl31anc.mm"
include "abssubd.mm"
include "le2addd.mm"
include "wne.mm"
include "2cnd.mm"
include "recnd.mm"
include "rpcnne0d.mm"
include "divass.mm"
include "syl3anc.mm"
include "2timesd.mm"
include "eqtrd.mm"
include "breqtrrd.mm"

theorem dchrisum0lem1b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cS: class S
  let c.1: class .1.
  let vm: setvar m
  let cF: class F
  let cG: class G
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
  let cE: class E
  let cK: class K
  let cP: class P
  let wps: wff ps
  let cT: class T
  let cR: class R
  let cU: class U
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
  disjoint N m
  disjoint N x
  disjoint N y
  disjoint d ph
  disjoint m ph
  disjoint ph x
  disjoint S d
  disjoint S m
  disjoint S x
  disjoint S y
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
  disjoint E d
  disjoint E m
  disjoint E x
  disjoint E y
  disjoint K k
  disjoint m r
  disjoint K m
  disjoint K r
  disjoint K y
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
  disjoint T d
  disjoint T m
  disjoint T n
  disjoint T p
  disjoint T r
  disjoint T x
  disjoint T y
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
  assert |- ( ( ( ph /\ x e. RR+ ) /\ d e. ( 1 ... ( |_ ` x ) ) ) -> ( abs ` sum_ m e. ( ( ( |_ ` x ) + 1 ) ... ( |_ ` ( ( x ^ 2 ) / d ) ) ) ( ( X ` ( L ` m ) ) / ( sqrt ` m ) ) ) <_ ( ( 2 x. C ) / ( sqrt ` x ) ) )

  proof
    wph
    vx
    cv
    #
    crp
    wcel
    #
    wa
    #
    vd
    cv
    #
    c1
    @0
    cfl
    cfv
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    @4
    c1
    caddc
    co
    #
    @0
    c2
    cexp
    co
    #
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
    vm
    cv
    #
    cL
    cfv
    #
    cX
    cfv
    #
    @13
    csqrt
    cfv
    #
    cdiv
    co
    #
    vm
    csu
    #
    cabs
    cfv
    #
    @11
    caddc
    cF
    c1
    cseq
    #
    cfv
    #
    cS
    cmin
    co
    #
    cabs
    cfv
    #
    cS
    @4
    @20
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    caddc
    co
    #
    c2
    cC
    cmul
    co
    #
    @0
    csqrt
    cfv
    #
    cdiv
    co
    #
    @7
    @18
    @7
    @12
    @17
    vm
    @7
    @8
    @11
    fzfid
    @7
    @13
    @12
    wcel
    @13
    c1
    @11
    cfz
    co
    #
    wcel
    #
    @17
    cc
    wcel
    #
    @7
    @12
    @31
    @13
    @7
    @5
    @12
    cun
    #
    @12
    @31
    @12
    @5
    ssun2
    @7
    @8
    c1
    cuz
    cfv
    #
    wcel
    @11
    @4
    cuz
    cfv
    wcel
    #
    @31
    @34
    wceq
    @7
    @8
    cn
    @35
    @2
    @8
    cn
    wcel
    #
    @6
    @2
    @4
    cn0
    wcel
    #
    @37
    @2
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
    @38
    @2
    @0
    wph
    @1
    simpr
    #
    rprege0d
    @0
    flge0nn0
    syl
    @4
    nn0p1nn
    syl
    adantr
    nnuz
    syl6eleq
    @7
    @0
    @10
    cle
    wbr
    #
    @36
    wph
    @3
    @0
    dchrisum0lem1a
    #
    simprd
    #
    @4
    c1
    @11
    fzsplit2
    syl2anc
    #
    syl5sseqr
    sselda
    @7
    @32
    wa
    #
    @15
    @16
    @46
    @13
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
    #
    @1
    @6
    @32
    wph
    cX
    cD
    c.1
    csn
    #
    wph
    cW
    cD
    @48
    cdif
    #
    cX
    cW
    cn
    @14
    vy
    cv
    #
    cfv
    @13
    cdiv
    co
    vm
    csu
    cc0
    wceq
    #
    vy
    @49
    crab
    @49
    rpvmasum2.w
    @51
    vy
    @49
    ssrab2
    eqsstri
    dchrisum0.b
    sseldi
    eldifad
    #
    ad3antrrr
    @32
    @13
    cz
    wcel
    #
    @7
    @13
    c1
    @11
    elfzelz
    adantl
    dchrzrhcl
    @46
    @16
    @46
    @13
    @46
    @13
    @32
    @13
    cn
    wcel
    #
    @7
    @13
    @11
    elfznn
    adantl
    #
    nnrpd
    rpsqrtcld
    #
    rpcnd
    @46
    @16
    @56
    rpne0d
    divcld
    #
    syldan
    fsumcl
    #
    abscld
    @7
    @23
    @26
    @7
    @22
    @7
    @21
    cS
    @7
    cn
    cc
    @11
    @20
    wph
    cn
    cc
    @20
    wf
    @1
    @6
    wph
    vm
    cF
    c1
    cn
    nnuz
    wph
    1zzd
    wph
    cn
    cc
    @13
    cF
    wph
    vm
    cn
    @17
    cc
    cF
    wph
    @54
    wa
    #
    @15
    @16
    @59
    @13
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
    @47
    @54
    @52
    adantr
    @54
    @53
    wph
    @13
    nnz
    adantl
    dchrzrhcl
    @59
    @16
    @59
    @13
    @54
    @13
    crp
    wcel
    wph
    @13
    nnrp
    adantl
    rpsqrtcld
    #
    rpcnd
    @59
    @16
    @60
    rpne0d
    divcld
    cF
    va
    cn
    va
    cv
    #
    cL
    cfv
    #
    cX
    cfv
    #
    @61
    csqrt
    cfv
    #
    cdiv
    co
    #
    cmpt
    vm
    cn
    @17
    cmpt
    dchrisum0lem1.f
    va
    vm
    cn
    @65
    @17
    va
    vm
    weq
    #
    @63
    @15
    @64
    @16
    cdiv
    @66
    @62
    @14
    cX
    @61
    @13
    cL
    fveq2
    fveq2d
    @61
    @13
    csqrt
    fveq2
    oveq12d
    #
    cbvmptv
    eqtri
    fmptd
    ffvelrnda
    serf
    ad2antrr
    #
    @7
    @4
    cn
    wcel
    #
    @36
    @11
    cn
    wcel
    @7
    @39
    c1
    @0
    cle
    wbr
    #
    @69
    @7
    @39
    cc0
    @0
    clt
    wbr
    #
    @2
    @39
    @71
    wa
    @6
    @2
    @0
    @41
    rpregt0d
    adantr
    simpld
    #
    @7
    c1
    @3
    @0
    @7
    1red
    #
    @7
    @3
    @6
    @3
    cn
    wcel
    #
    @2
    @3
    @4
    elfznn
    #
    adantl
    #
    nnred
    @72
    @7
    @3
    @76
    nnge1d
    @2
    @6
    @74
    @3
    @0
    cle
    wbr
    #
    @2
    @39
    @6
    @74
    @77
    wa
    wb
    @2
    @0
    @41
    rpred
    @3
    @0
    fznnfl
    syl
    simplbda
    letrd
    #
    @0
    flge1nn
    syl2anc
    #
    @44
    @11
    @4
    eluznn
    syl2anc
    #
    ffvelrnd
    #
    wph
    cS
    cc
    wcel
    #
    @1
    @6
    wph
    @20
    cS
    cli
    wbr
    @82
    dchrisum0.s
    cS
    @20
    climcl
    syl
    ad2antrr
    #
    subcld
    abscld
    #
    @7
    @25
    @7
    cS
    @24
    @83
    @7
    cn
    cc
    @4
    @20
    @68
    @79
    ffvelrnd
    #
    subcld
    abscld
    #
    readdcld
    @2
    @30
    cr
    wcel
    @6
    @2
    @28
    @29
    wph
    @28
    cr
    wcel
    #
    @1
    wph
    c2
    cr
    wcel
    cC
    cr
    wcel
    #
    @87
    2re
    wph
    @88
    cc0
    cC
    cle
    wbr
    #
    wph
    cC
    cc0
    cpnf
    cico
    co
    wcel
    @88
    @89
    wa
    #
    dchrisum0.c
    cC
    elrege0
    sylib
    #
    simpld
    #
    c2
    cC
    remulcl
    sylancr
    adantr
    @2
    @0
    @41
    rpsqrtcld
    #
    rerpdivcld
    adantr
    @7
    @19
    @21
    @24
    cmin
    co
    #
    cabs
    cfv
    @27
    cle
    @7
    @18
    @94
    cabs
    @7
    @5
    @17
    vm
    csu
    #
    @18
    caddc
    co
    #
    @95
    cmin
    co
    @18
    @94
    @7
    @95
    @18
    @7
    @95
    @24
    cc
    @7
    @17
    vm
    cF
    c1
    @4
    @7
    @13
    @5
    wcel
    #
    @32
    @13
    cF
    cfv
    @17
    wceq
    #
    @7
    @5
    @31
    @13
    @7
    @34
    @5
    @31
    @5
    @12
    ssun1
    @45
    syl5sseqr
    sselda
    #
    @46
    @54
    @98
    @55
    va
    @13
    @65
    @17
    cn
    cF
    @67
    dchrisum0lem1.f
    @63
    @64
    cdiv
    ovex
    fvmpt3i
    syl
    #
    syldan
    @7
    @4
    cn
    @35
    @79
    nnuz
    syl6eleq
    @7
    @97
    @32
    @33
    @99
    @57
    syldan
    fsumser
    #
    @85
    eqeltrd
    @58
    pncan2d
    @7
    @96
    @21
    @95
    @24
    cmin
    @7
    @31
    @17
    vm
    csu
    @96
    @21
    @7
    @5
    @12
    @17
    @31
    vm
    @7
    @4
    @8
    clt
    wbr
    @5
    @12
    cin
    c0
    wceq
    @7
    @4
    @7
    @39
    @4
    cr
    wcel
    @72
    @0
    reflcl
    syl
    ltp1d
    c1
    @4
    @8
    @11
    fzdisj
    syl
    @45
    @7
    c1
    @11
    fzfid
    @57
    fsumsplit
    @7
    @17
    vm
    cF
    c1
    @11
    @100
    @7
    @11
    cn
    @35
    @80
    nnuz
    syl6eleq
    @57
    fsumser
    eqtr3d
    @101
    oveq12d
    eqtr3d
    fveq2d
    @7
    @21
    @24
    cS
    @81
    @85
    @83
    abs3difd
    eqbrtrd
    @7
    @27
    cC
    @29
    cdiv
    co
    #
    @102
    caddc
    co
    #
    @30
    cle
    @7
    @23
    @26
    @102
    @102
    @84
    @86
    @7
    cC
    @29
    wph
    @88
    @1
    @6
    @92
    ad2antrr
    #
    @7
    @0
    wph
    @1
    @6
    simplr
    #
    rpsqrtcld
    #
    rerpdivcld
    #
    @107
    @7
    @23
    cC
    @10
    csqrt
    cfv
    #
    cdiv
    co
    #
    @102
    @84
    @7
    cC
    @108
    @104
    @7
    @10
    @7
    @9
    @3
    @2
    @9
    crp
    wcel
    #
    @6
    @2
    @1
    c2
    cz
    wcel
    @110
    @41
    2z
    @0
    c2
    rpexpcl
    sylancl
    #
    adantr
    @7
    @3
    @76
    nnrpd
    rpdivcld
    #
    rpsqrtcld
    #
    rerpdivcld
    @107
    @7
    @10
    c1
    cpnf
    cico
    co
    #
    wcel
    #
    @50
    cfl
    cfv
    #
    @20
    cfv
    #
    cS
    cmin
    co
    #
    cabs
    cfv
    #
    cC
    @50
    csqrt
    cfv
    #
    cdiv
    co
    #
    cle
    wbr
    #
    vy
    @114
    wral
    #
    @23
    @109
    cle
    wbr
    #
    @7
    @10
    cr
    wcel
    #
    c1
    @10
    cle
    wbr
    #
    @115
    @2
    @9
    cr
    wcel
    @74
    @125
    @6
    @2
    @9
    @111
    rpred
    @75
    @9
    @3
    nndivre
    syl2an
    #
    @7
    c1
    @0
    @10
    @73
    @72
    @127
    @78
    @7
    @42
    @36
    @43
    simpld
    #
    letrd
    c1
    cr
    wcel
    #
    @115
    @125
    @126
    wa
    wb
    1re
    c1
    @10
    elicopnf
    ax-mp
    sylanbrc
    wph
    @123
    @1
    @6
    dchrisum0.1
    ad2antrr
    #
    @122
    @124
    vy
    @10
    @114
    @50
    @10
    wceq
    #
    @119
    @23
    @121
    @109
    cle
    @131
    @118
    @22
    cabs
    @131
    @117
    @21
    cS
    cmin
    @131
    @116
    @11
    @20
    @50
    @10
    cfl
    fveq2
    fveq2d
    oveq1d
    fveq2d
    @131
    @120
    @108
    cC
    cdiv
    @50
    @10
    csqrt
    fveq2
    oveq2d
    breq12d
    rspcv
    sylc
    @7
    @29
    cr
    wcel
    cc0
    @29
    clt
    wbr
    wa
    @108
    cr
    wcel
    cc0
    @108
    clt
    wbr
    wa
    @90
    @29
    @108
    cle
    wbr
    #
    @109
    @102
    cle
    wbr
    @7
    @29
    @106
    rpregt0d
    @7
    @108
    @113
    rpregt0d
    wph
    @90
    @1
    @6
    @91
    ad2antrr
    @7
    @42
    @132
    @128
    @7
    @40
    @125
    cc0
    @10
    cle
    wbr
    wa
    @42
    @132
    wb
    @7
    @0
    @105
    rprege0d
    @7
    @10
    @112
    rprege0d
    @0
    @10
    sqrtle
    syl2anc
    mpbid
    @29
    @108
    cC
    lediv2a
    syl31anc
    letrd
    @7
    @26
    @24
    cS
    cmin
    co
    #
    cabs
    cfv
    #
    @102
    cle
    @7
    cS
    @24
    @83
    @85
    abssubd
    @7
    @0
    @114
    wcel
    #
    @123
    @134
    @102
    cle
    wbr
    #
    @7
    @39
    @70
    @135
    @72
    @78
    @129
    @135
    @39
    @70
    wa
    wb
    1re
    c1
    @0
    elicopnf
    ax-mp
    sylanbrc
    @130
    @122
    @136
    vy
    @0
    @114
    vy
    vx
    weq
    #
    @119
    @134
    @121
    @102
    cle
    @137
    @118
    @133
    cabs
    @137
    @117
    @24
    cS
    cmin
    @137
    @116
    @4
    @20
    @50
    @0
    cfl
    fveq2
    fveq2d
    oveq1d
    fveq2d
    @137
    @120
    @29
    cC
    cdiv
    @50
    @0
    csqrt
    fveq2
    oveq2d
    breq12d
    rspcv
    sylc
    eqbrtrd
    le2addd
    @7
    @30
    c2
    @102
    cmul
    co
    #
    @103
    @7
    c2
    cc
    wcel
    cC
    cc
    wcel
    #
    @29
    cc
    wcel
    @29
    cc0
    wne
    wa
    #
    @30
    @138
    wceq
    @7
    2cnd
    @2
    @139
    @6
    @2
    cC
    wph
    @88
    @1
    @92
    adantr
    recnd
    adantr
    @2
    @140
    @6
    @2
    @29
    @93
    rpcnne0d
    adantr
    c2
    cC
    @29
    divass
    syl3anc
    @7
    @102
    @7
    @102
    @107
    recnd
    2timesd
    eqtrd
    breqtrrd
    letrd
end
