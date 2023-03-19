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
include "caddc.mm"
include "cmul.mm"
include "cvv.mm"
include "1red.mm"
include "wcel.mm"
include "wa.mm"
include "sumex.mm"
include "a1i.mm"
include "cn.mm"
include "cmpt.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "cmin.mm"
include "cabs.mm"
include "cle.mm"
include "cpnf.mm"
include "cico.mm"
include "wral.mm"
include "cc0.mm"
include "wrex.mm"
include "wex.mm"
include "co1.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "difss.mm"
include "sstri.mm"
include "sseldi.mm"
include "wne.mm"
include "eldifsni.mm"
include "syl.mm"
include "eqid.mm"
include "dchrmusumlema.mm"
include "crli.mm"
include "adantr.mm"
include "cdm.mm"
include "divsqrsum.mm"
include "cc.mm"
include "wf.mm"
include "cr.mm"
include "wss.mm"
include "divsqrsumf.mm"
include "ax-resscn.mm"
include "fss.mm"
include "mp2an.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "rpsup.mm"
include "rlimdm.mm"
include "mpbii.mm"
include "simprl.mm"
include "simprrl.mm"
include "simprrr.mm"
include "dchrisum0lem2.mm"
include "rexlimdvaa.mm"
include "exlimdv.mm"
include "mpd.mm"
include "dchrisum0lem1.mm"
include "o1add2.mm"
include "ovexd.mm"
include "fzfid.mm"
include "ad2antrr.mm"
include "cz.mm"
include "elfzelz.mm"
include "adantl.mm"
include "dchrzrhcl.mm"
include "elfznn.mm"
include "nnrpd.mm"
include "rpmulcl.mm"
include "syl2an.mm"
include "rpsqrtcld.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divcld.mm"
include "fsumcl.mm"
include "abscld.mm"
include "adantrr.mm"
include "rprege0d.mm"
include "sqrtmul.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "rpcnne0d.mm"
include "divdiv1.mm"
include "syl3anc.mm"
include "eqtr4d.mm"
include "sumeq2dv.mm"
include "cin.mm"
include "c0.mm"
include "simpr.mm"
include "rpred.mm"
include "reflcl.mm"
include "ltp1d.mm"
include "fzdisj.mm"
include "cuz.mm"
include "cun.mm"
include "cn0.mm"
include "flge0nn0.mm"
include "nn0p1nn.mm"
include "3syl.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "2z.mm"
include "rpexpcl.mm"
include "sylancl.mm"
include "recnd.mm"
include "mulid1d.mm"
include "simprr.mm"
include "wb.mm"
include "rpregt0.mm"
include "ad2antrl.mm"
include "lemul2.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"
include "sqvald.mm"
include "breqtrrd.mm"
include "flword2.mm"
include "fzsplit2.mm"
include "eqeltrrd.mm"
include "adantlrr.mm"
include "fsumsplit.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "eqle.mm"
include "o1le.mm"

theorem dchrisum0lem3
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
  assert |- ( ph -> ( x e. RR+ |-> sum_ m e. ( 1 ... ( |_ ` ( x ^ 2 ) ) ) sum_ d e. ( 1 ... ( |_ ` ( ( x ^ 2 ) / m ) ) ) ( ( X ` ( L ` m ) ) / ( sqrt ` ( m x. d ) ) ) ) e. O(1) )

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
    @1
    c1
    caddc
    co
    #
    @3
    cfl
    cfv
    #
    cfz
    co
    #
    @13
    vm
    csu
    #
    caddc
    co
    #
    c1
    @16
    cfz
    co
    #
    @6
    @8
    @4
    @10
    cmul
    co
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
    c1
    cvv
    wph
    1red
    wph
    vx
    crp
    @14
    @18
    cvv
    @14
    cvv
    wcel
    wph
    @0
    crp
    wcel
    #
    wa
    #
    @2
    @13
    vm
    sumex
    a1i
    @18
    cvv
    wcel
    @27
    @17
    @13
    vm
    sumex
    a1i
    wph
    caddc
    va
    cn
    va
    cv
    #
    cL
    cfv
    cX
    cfv
    @28
    cdiv
    co
    cmpt
    #
    c1
    cseq
    #
    vt
    cv
    #
    cli
    wbr
    #
    vy
    cv
    #
    cfl
    cfv
    #
    @30
    cfv
    @31
    cmin
    co
    cabs
    cfv
    vc
    cv
    #
    @33
    cdiv
    co
    cle
    wbr
    vy
    c1
    cpnf
    cico
    co
    #
    wral
    #
    wa
    #
    vc
    cc0
    cpnf
    cico
    co
    #
    wrex
    #
    vt
    wex
    vx
    crp
    @14
    cmpt
    co1
    wcel
    #
    wph
    vy
    vt
    cD
    c.1
    @29
    cG
    cL
    cN
    cX
    cZ
    va
    vc
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    rpvmasum2.g
    rpvmasum2.d
    rpvmasum2.1
    wph
    cW
    cD
    cX
    cW
    cD
    c.1
    csn
    #
    cdif
    #
    cD
    cW
    cn
    @7
    @33
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
    @43
    crab
    @43
    rpvmasum2.w
    @44
    vy
    @43
    ssrab2
    eqsstri
    #
    cD
    @42
    difss
    sstri
    dchrisum0.b
    sseldi
    #
    wph
    cX
    @43
    wcel
    cX
    c.1
    wne
    wph
    cW
    @43
    cX
    @45
    dchrisum0.b
    sseldi
    cX
    cD
    c.1
    eldifsni
    syl
    @29
    eqid
    #
    dchrmusumlema
    wph
    @40
    @41
    vt
    wph
    @38
    @41
    vc
    @39
    wph
    @35
    @39
    wcel
    #
    @38
    wa
    #
    wa
    vx
    vy
    cC
    cD
    cS
    @31
    vy
    crp
    c1
    @34
    cfz
    co
    c1
    @11
    cdiv
    co
    vd
    csu
    c2
    @33
    csqrt
    cfv
    #
    cmul
    co
    cmin
    co
    cmpt
    #
    crli
    cfv
    #
    c.1
    vm
    @35
    cF
    cG
    @51
    @29
    cL
    cN
    cW
    cX
    cZ
    va
    vd
    rpvmasum.z
    rpvmasum.l
    wph
    cN
    cn
    wcel
    @49
    rpvmasum.a
    adantr
    rpvmasum2.g
    rpvmasum2.d
    rpvmasum2.1
    rpvmasum2.w
    wph
    cX
    cW
    wcel
    @49
    dchrisum0.b
    adantr
    dchrisum0lem1.f
    wph
    cC
    @39
    wcel
    @49
    dchrisum0.c
    adantr
    wph
    caddc
    cF
    c1
    cseq
    #
    cS
    cli
    wbr
    @49
    dchrisum0.s
    adantr
    wph
    @34
    @53
    cfv
    cS
    cmin
    co
    cabs
    cfv
    cC
    @50
    cdiv
    co
    cle
    wbr
    vy
    @36
    wral
    @49
    dchrisum0.1
    adantr
    @51
    eqid
    #
    wph
    @51
    @52
    crli
    wbr
    #
    @49
    wph
    @51
    crli
    cdm
    wcel
    @55
    vy
    vd
    @51
    @54
    divsqrsum
    wph
    crp
    @51
    crp
    cc
    @51
    wf
    #
    wph
    crp
    cr
    @51
    wf
    cr
    cc
    wss
    @56
    vy
    vd
    @51
    @54
    divsqrsumf
    ax-resscn
    crp
    cr
    cc
    @51
    fss
    mp2an
    a1i
    crp
    cxr
    clt
    csup
    cpnf
    wceq
    wph
    rpsup
    a1i
    rlimdm
    mpbii
    adantr
    @47
    wph
    @48
    @38
    simprl
    wph
    @48
    @32
    @37
    simprrl
    wph
    @48
    @32
    @37
    simprrr
    dchrisum0lem2
    rexlimdvaa
    exlimdv
    mpd
    wph
    vx
    vy
    cC
    cD
    cS
    c.1
    vm
    cF
    cG
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
    dchrisum0lem1
    o1add2
    @27
    @14
    @18
    caddc
    ovexd
    @27
    @20
    @24
    vm
    @27
    c1
    @16
    fzfid
    @27
    @4
    @20
    wcel
    #
    wa
    #
    @6
    @23
    vd
    @58
    c1
    @5
    fzfid
    @58
    @10
    @6
    wcel
    #
    wa
    #
    @8
    @22
    @58
    @8
    cc
    wcel
    #
    @59
    @58
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
    @26
    @57
    @46
    ad2antrr
    @57
    @4
    cz
    wcel
    @27
    @4
    c1
    @16
    elfzelz
    adantl
    dchrzrhcl
    adantr
    #
    @60
    @22
    @60
    @21
    @58
    @4
    crp
    wcel
    @10
    crp
    wcel
    @21
    crp
    wcel
    @59
    @58
    @4
    @57
    @4
    cn
    wcel
    #
    @27
    @4
    @16
    elfznn
    adantl
    #
    nnrpd
    @59
    @10
    @10
    @5
    elfznn
    #
    nnrpd
    @4
    @10
    rpmulcl
    syl2an
    rpsqrtcld
    #
    rpcnd
    @60
    @22
    @66
    rpne0d
    divcld
    fsumcl
    #
    fsumcl
    #
    wph
    @26
    c1
    @0
    cle
    wbr
    #
    wa
    wa
    #
    @25
    cabs
    cfv
    #
    cr
    wcel
    #
    @71
    @19
    cabs
    cfv
    #
    wceq
    @71
    @73
    cle
    wbr
    wph
    @26
    @72
    @69
    @27
    @25
    @68
    abscld
    adantrr
    @70
    @25
    @19
    cabs
    @70
    @25
    @20
    @13
    vm
    csu
    #
    @19
    wph
    @26
    @25
    @74
    wceq
    @69
    @27
    @20
    @24
    @13
    vm
    @58
    @6
    @23
    @12
    vd
    @60
    @23
    @8
    @9
    @11
    cmul
    co
    #
    cdiv
    co
    #
    @12
    @60
    @22
    @75
    @8
    cdiv
    @60
    @4
    cr
    wcel
    cc0
    @4
    cle
    wbr
    wa
    @10
    cr
    wcel
    cc0
    @10
    cle
    wbr
    wa
    @22
    @75
    wceq
    @60
    @4
    @60
    @4
    @58
    @63
    @59
    @64
    adantr
    nnrpd
    #
    rprege0d
    @60
    @10
    @60
    @10
    @59
    @10
    cn
    wcel
    @58
    @65
    adantl
    nnrpd
    #
    rprege0d
    @4
    @10
    sqrtmul
    syl2anc
    oveq2d
    @60
    @61
    @9
    cc
    wcel
    @9
    cc0
    wne
    wa
    @11
    cc
    wcel
    @11
    cc0
    wne
    wa
    @12
    @76
    wceq
    @62
    @60
    @9
    @60
    @4
    @77
    rpsqrtcld
    rpcnne0d
    @60
    @11
    @60
    @10
    @78
    rpsqrtcld
    rpcnne0d
    @8
    @9
    @11
    divdiv1
    syl3anc
    eqtr4d
    sumeq2dv
    #
    sumeq2dv
    adantrr
    @70
    @2
    @17
    @13
    @20
    vm
    wph
    @26
    @2
    @17
    cin
    c0
    wceq
    #
    @69
    @27
    @1
    @15
    clt
    wbr
    @80
    @27
    @1
    @27
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    @27
    @0
    wph
    @26
    simpr
    #
    rpred
    #
    @0
    reflcl
    syl
    ltp1d
    c1
    @1
    @15
    @16
    fzdisj
    syl
    adantrr
    @70
    @15
    c1
    cuz
    cfv
    #
    wcel
    #
    @16
    @1
    cuz
    cfv
    wcel
    #
    @20
    @2
    @17
    cun
    wceq
    wph
    @26
    @85
    @69
    @27
    @15
    cn
    @84
    @27
    @81
    cc0
    @0
    cle
    wbr
    wa
    @1
    cn0
    wcel
    @15
    cn
    wcel
    @27
    @0
    @82
    rprege0d
    @0
    flge0nn0
    @1
    nn0p1nn
    3syl
    nnuz
    syl6eleq
    adantrr
    @70
    @81
    @3
    cr
    wcel
    @0
    @3
    cle
    wbr
    @86
    wph
    @26
    @81
    @69
    @83
    adantrr
    #
    @70
    @3
    wph
    @26
    @3
    crp
    wcel
    #
    @69
    @27
    @26
    c2
    cz
    wcel
    @88
    @82
    2z
    @0
    c2
    rpexpcl
    sylancl
    adantrr
    rpred
    @70
    @0
    @0
    @0
    cmul
    co
    #
    @3
    cle
    @70
    @0
    c1
    cmul
    co
    #
    @0
    @89
    cle
    @70
    @0
    @70
    @0
    @87
    recnd
    #
    mulid1d
    @70
    @69
    @90
    @89
    cle
    wbr
    #
    wph
    @26
    @69
    simprr
    @70
    c1
    cr
    wcel
    @81
    @81
    cc0
    @0
    clt
    wbr
    wa
    #
    @69
    @92
    wb
    @70
    1red
    @87
    @26
    @93
    wph
    @69
    @0
    rpregt0
    ad2antrl
    c1
    @0
    @0
    lemul2
    syl3anc
    mpbid
    eqbrtrrd
    @70
    @0
    @91
    sqvald
    breqtrrd
    @0
    @3
    flword2
    syl3anc
    @1
    c1
    @16
    fzsplit2
    syl2anc
    @70
    c1
    @16
    fzfid
    wph
    @26
    @57
    @13
    cc
    wcel
    @69
    @58
    @24
    @13
    cc
    @79
    @67
    eqeltrrd
    adantlrr
    fsumsplit
    eqtrd
    fveq2d
    @71
    @73
    eqle
    syl2anc
    o1le
end
