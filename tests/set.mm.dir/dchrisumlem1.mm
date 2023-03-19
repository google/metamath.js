include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "cabs.mm"
include "cmo.mm"
include "cle.mm"
include "cdiv.mm"
include "cfl.mm"
include "cmul.mm"
include "caddc.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "fzodisj.mm"
include "a1i.mm"
include "cfz.mm"
include "cun.mm"
include "wbr.mm"
include "nnnn0d.mm"
include "adantr.mm"
include "cr.mm"
include "nn0re.mm"
include "adantl.mm"
include "cn.mm"
include "nndivred.mm"
include "nnrpd.mm"
include "nn0ge0.mm"
include "divge0d.mm"
include "flge0nn0.mm"
include "syl2anc.mm"
include "nn0mulcld.mm"
include "flle.mm"
include "syl.mm"
include "reflcl.mm"
include "lemuldiv2d.mm"
include "mpbird.mm"
include "wb.mm"
include "fznn0.mm"
include "mpbir2and.mm"
include "fzosplit.mm"
include "cfn.mm"
include "fzofi.mm"
include "ad2antrr.mm"
include "cz.mm"
include "elfzoelz.mm"
include "dchrzrhcl.mm"
include "fsumsplit.mm"
include "wi.mm"
include "c1.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "weq.mm"
include "nncnd.mm"
include "mul01d.mm"
include "fzo0.mm"
include "syl6eq.mm"
include "sum0.mm"
include "oveq1.mm"
include "lep1d.mm"
include "clt.mm"
include "peano2re.mm"
include "nnred.mm"
include "nngt0d.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "cuz.mm"
include "nn0mulcl.mm"
include "sylan.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "nn0p1nn.mm"
include "nnmulcl.mm"
include "syl2an.mm"
include "nnzd.mm"
include "elfz5.mm"
include "recnd.mm"
include "1cnd.mm"
include "adddid.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "wral.mm"
include "cmin.mm"
include "nn0zd.mm"
include "nn0z.mm"
include "zaddcl.mm"
include "peano2zm.mm"
include "ad3antrrr.mm"
include "elfzelz.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "fsumshftm.mm"
include "fzoval.mm"
include "zcnd.mm"
include "subidd.mm"
include "sub32d.mm"
include "cc.mm"
include "nn0cn.mm"
include "pncan2d.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "3eqtr4d.mm"
include "cdvds.mm"
include "dvdsmul1.mm"
include "breqtrrd.mm"
include "syl2anr.mm"
include "zndvds.mm"
include "syl3anc.mm"
include "sumeq2dv.mm"
include "cbvsumv.mm"
include "ralrimiva.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "cbs.mm"
include "cif.mm"
include "cres.mm"
include "wne.mm"
include "nnne0d.mm"
include "ifnefalse.mm"
include "syl6eqel.mm"
include "wf1o.mm"
include "eqid.mm"
include "czrh.mm"
include "reseq1i.mm"
include "znf1o.mm"
include "fvres.mm"
include "dchrf.mm"
include "ffvelrnda.mm"
include "fsumf1o.mm"
include "cphi.mm"
include "dchrsum.mm"
include "3eqtr3rd.mm"
include "3eqtrd.mm"
include "00id.mm"
include "syl6req.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"
include "syldan.mm"
include "crp.mm"
include "modval.mm"
include "nn0cnd.mm"
include "pncan3d.mm"
include "eqtr2d.mm"
include "zmodcl.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "fsumcl.mm"
include "addid2d.mm"
include "zmodfzo.mm"
include "breq1d.mm"
include "eqbrtrd.mm"

theorem dchrisumlem1
  let wph: wff ph
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cL: class L
  let cM: class M
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vm: setvar m
  let vk: setvar k
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vc: setvar c
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vp: setvar p
  let vt: setvar t
  let vd: setvar d
  let cC: class C
  let ve: setvar e
  let vr: setvar r
  let cI: class I
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vq: setvar q
  let vv: setvar v
  let cE: class E
  let cK: class K
  let cP: class P
  let wps: wff ps
  let cT: class T
  let cS: class S
  let cW: class W
  assume rpvmasum.z: |- Z = ( Z/nZ ` N )
  assume rpvmasum.l: |- L = ( ZRHom ` Z )
  assume rpvmasum.a: |- ( ph -> N e. NN )
  assume rpvmasum.g: |- G = ( DChr ` N )
  assume rpvmasum.d: |- D = ( Base ` G )
  assume rpvmasum.1: |- .1. = ( 0g ` G )
  assume dchrisum.b: |- ( ph -> X e. D )
  assume dchrisum.n1: |- ( ph -> X =/= .1. )
  assume dchrisum.2: |- ( n = x -> A = B )
  assume dchrisum.3: |- ( ph -> M e. NN )
  assume dchrisum.4: |- ( ( ph /\ n e. RR+ ) -> A e. RR )
  assume dchrisum.5: |- ( ( ph /\ ( n e. RR+ /\ x e. RR+ ) /\ ( M <_ n /\ n <_ x ) ) -> B <_ A )
  assume dchrisum.6: |- ( ph -> ( n e. RR+ |-> A ) ~~>r 0 )
  assume dchrisum.7: |- F = ( n e. NN |-> ( ( X ` ( L ` n ) ) x. A ) )
  assume dchrisum.9: |- ( ph -> R e. RR )
  assume dchrisum.10: |- ( ph -> A. u e. ( 0 ..^ N ) ( abs ` sum_ n e. ( 0 ..^ u ) ( X ` ( L ` n ) ) ) <_ R )

  disjoint n u
  disjoint n x
  disjoint u x
  disjoint .1. n
  disjoint .1. x
  disjoint F n
  disjoint F u
  disjoint F x
  disjoint A x
  disjoint N n
  disjoint N u
  disjoint N x
  disjoint n ph
  disjoint ph u
  disjoint ph x
  disjoint R n
  disjoint R u
  disjoint R x
  disjoint U n
  disjoint U u
  disjoint U x
  disjoint B n
  disjoint Z n
  disjoint Z x
  disjoint D n
  disjoint D x
  disjoint L n
  disjoint L u
  disjoint L x
  disjoint M n
  disjoint M u
  disjoint M x
  disjoint X n
  disjoint X u
  disjoint X x
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
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
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
  disjoint .1. y
  disjoint .1. z
  disjoint d m
  disjoint d n
  disjoint d x
  disjoint d y
  disjoint C d
  disjoint C m
  disjoint C n
  disjoint C x
  disjoint C y
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
  disjoint F y
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
  disjoint a x
  disjoint a y
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
  disjoint N m
  disjoint n q
  disjoint N p
  disjoint q r
  disjoint q u
  disjoint N q
  disjoint N r
  disjoint N t
  disjoint N y
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
  disjoint R z
  disjoint S c
  disjoint S d
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S r
  disjoint S t
  disjoint S x
  disjoint S y
  disjoint U k
  disjoint U m
  disjoint U p
  disjoint U z
  disjoint b r
  disjoint B b
  disjoint B c
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B m
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
  disjoint Z y
  disjoint Z z
  disjoint D c
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D k
  disjoint D m
  disjoint D t
  disjoint D y
  disjoint D z
  disjoint a n
  disjoint a r
  disjoint a u
  disjoint L a
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
  disjoint L v
  disjoint L y
  disjoint L z
  disjoint M c
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint M m
  disjoint M r
  disjoint M z
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X m
  disjoint X r
  disjoint X t
  disjoint X v
  disjoint X y
  disjoint X z
  assert |- ( ( ph /\ U e. NN0 ) -> ( abs ` sum_ n e. ( 0 ..^ U ) ( X ` ( L ` n ) ) ) <_ R )

  proof
    wph
    cU
    cn0
    wcel
    #
    wa
    #
    cc0
    cU
    cfzo
    co
    #
    vn
    cv
    #
    cL
    cfv
    #
    cX
    cfv
    #
    vn
    csu
    #
    cabs
    cfv
    cc0
    cU
    cN
    cmo
    co
    #
    cfzo
    co
    #
    @5
    vn
    csu
    #
    cabs
    cfv
    #
    cR
    cle
    @1
    @6
    @9
    cabs
    @1
    @6
    cc0
    cN
    cU
    cN
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cfzo
    co
    #
    @5
    vn
    csu
    #
    @13
    cU
    cfzo
    co
    #
    @5
    vn
    csu
    #
    caddc
    co
    cc0
    @9
    caddc
    co
    @9
    @1
    @14
    @16
    @5
    @2
    vn
    @14
    @16
    cin
    c0
    wceq
    @1
    cc0
    @13
    cU
    fzodisj
    a1i
    @1
    @13
    cc0
    cU
    cfz
    co
    wcel
    #
    @2
    @14
    @16
    cun
    wceq
    @1
    @18
    @13
    cn0
    wcel
    #
    @13
    cU
    cle
    wbr
    #
    @1
    cN
    @12
    wph
    cN
    cn0
    wcel
    #
    @0
    wph
    cN
    rpvmasum.a
    nnnn0d
    #
    adantr
    @1
    @11
    cr
    wcel
    #
    cc0
    @11
    cle
    wbr
    @12
    cn0
    wcel
    #
    @1
    cU
    cN
    @0
    cU
    cr
    wcel
    #
    wph
    cU
    nn0re
    adantl
    #
    wph
    cN
    cn
    wcel
    #
    @0
    rpvmasum.a
    adantr
    #
    nndivred
    #
    @1
    cU
    cN
    @26
    @1
    cN
    @28
    nnrpd
    #
    @0
    cc0
    cU
    cle
    wbr
    wph
    cU
    nn0ge0
    adantl
    divge0d
    @11
    flge0nn0
    syl2anc
    #
    nn0mulcld
    #
    @1
    @20
    @12
    @11
    cle
    wbr
    #
    @1
    @23
    @33
    @29
    @11
    flle
    syl
    @1
    @12
    cU
    cN
    @1
    @23
    @12
    cr
    wcel
    @29
    @11
    reflcl
    syl
    @26
    @30
    lemuldiv2d
    mpbird
    @0
    @18
    @19
    @20
    wa
    wb
    wph
    @13
    cU
    fznn0
    adantl
    mpbir2and
    cc0
    cU
    @13
    fzosplit
    syl
    @2
    cfn
    wcel
    @1
    cc0
    cU
    fzofi
    a1i
    @1
    @3
    @2
    wcel
    #
    wa
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
    @0
    @34
    dchrisum.b
    ad2antrr
    @34
    @3
    cz
    wcel
    #
    @1
    @3
    cc0
    cU
    elfzoelz
    adantl
    dchrzrhcl
    fsumsplit
    @1
    @15
    cc0
    @17
    @9
    caddc
    wph
    @0
    @24
    @15
    cc0
    wceq
    #
    @31
    @24
    wph
    @37
    wph
    cc0
    cN
    vk
    cv
    #
    cmul
    co
    #
    cfzo
    co
    #
    @5
    vn
    csu
    #
    cc0
    wceq
    #
    wi
    wph
    cc0
    cN
    cc0
    cmul
    co
    #
    cfzo
    co
    #
    @5
    vn
    csu
    #
    cc0
    wceq
    #
    wi
    wph
    cc0
    cN
    vm
    cv
    #
    cmul
    co
    #
    cfzo
    co
    #
    @5
    vn
    csu
    #
    cc0
    wceq
    #
    wi
    wph
    cc0
    cN
    @47
    c1
    caddc
    co
    #
    cmul
    co
    #
    cfzo
    co
    #
    @5
    vn
    csu
    #
    cc0
    wceq
    #
    wi
    wph
    @37
    wi
    vk
    vm
    @12
    @38
    cc0
    wceq
    #
    @42
    @46
    wph
    @57
    @41
    @45
    cc0
    @57
    @40
    @44
    @5
    vn
    @57
    @39
    @43
    cc0
    cfzo
    @38
    cc0
    cN
    cmul
    oveq2
    oveq2d
    sumeq1d
    eqeq1d
    imbi2d
    vk
    vm
    weq
    #
    @42
    @51
    wph
    @58
    @41
    @50
    cc0
    @58
    @40
    @49
    @5
    vn
    @58
    @39
    @48
    cc0
    cfzo
    @38
    @47
    cN
    cmul
    oveq2
    oveq2d
    sumeq1d
    eqeq1d
    imbi2d
    @38
    @52
    wceq
    #
    @42
    @56
    wph
    @59
    @41
    @55
    cc0
    @59
    @40
    @54
    @5
    vn
    @59
    @39
    @53
    cc0
    cfzo
    @38
    @52
    cN
    cmul
    oveq2
    oveq2d
    sumeq1d
    eqeq1d
    imbi2d
    @38
    @12
    wceq
    #
    @42
    @37
    wph
    @60
    @41
    @15
    cc0
    @60
    @40
    @14
    @5
    vn
    @60
    @39
    @13
    cc0
    cfzo
    @38
    @12
    cN
    cmul
    oveq2
    oveq2d
    sumeq1d
    eqeq1d
    imbi2d
    wph
    @45
    c0
    @5
    vn
    csu
    cc0
    wph
    @44
    c0
    @5
    vn
    wph
    @44
    cc0
    cc0
    cfzo
    co
    c0
    wph
    @43
    cc0
    cc0
    cfzo
    wph
    cN
    wph
    cN
    rpvmasum.a
    nncnd
    mul01d
    oveq2d
    cc0
    fzo0
    syl6eq
    sumeq1d
    @5
    vn
    sum0
    syl6eq
    @47
    cn0
    wcel
    #
    wph
    @51
    @56
    wph
    @61
    @51
    @56
    wi
    @51
    @56
    wph
    @61
    wa
    #
    @50
    @48
    @53
    cfzo
    co
    #
    @5
    vn
    csu
    #
    caddc
    co
    #
    cc0
    @64
    caddc
    co
    #
    wceq
    @50
    cc0
    @64
    caddc
    oveq1
    @62
    @55
    @65
    cc0
    @66
    @62
    @49
    @63
    @5
    @54
    vn
    @49
    @63
    cin
    c0
    wceq
    @62
    cc0
    @48
    @53
    fzodisj
    a1i
    @62
    @48
    cc0
    @53
    cfz
    co
    wcel
    #
    @54
    @49
    @63
    cun
    wceq
    @62
    @67
    @48
    @53
    cle
    wbr
    #
    @62
    @47
    @52
    cle
    wbr
    #
    @68
    @62
    @47
    @61
    @47
    cr
    wcel
    #
    wph
    @47
    nn0re
    adantl
    #
    lep1d
    @62
    @70
    @52
    cr
    wcel
    #
    cN
    cr
    wcel
    cc0
    cN
    clt
    wbr
    @69
    @68
    wb
    @71
    @62
    @70
    @72
    @71
    @47
    peano2re
    syl
    @62
    cN
    wph
    @27
    @61
    rpvmasum.a
    adantr
    #
    nnred
    @62
    cN
    @73
    nngt0d
    @47
    @52
    cN
    lemul2
    syl112anc
    mpbid
    @62
    @48
    cc0
    cuz
    cfv
    #
    wcel
    @53
    cz
    wcel
    @67
    @68
    wb
    @62
    @48
    cn0
    @74
    wph
    @21
    @61
    @48
    cn0
    wcel
    @22
    cN
    @47
    nn0mulcl
    sylan
    #
    nn0uz
    syl6eleq
    @62
    @53
    wph
    @27
    @52
    cn
    wcel
    @53
    cn
    wcel
    @61
    rpvmasum.a
    @47
    nn0p1nn
    cN
    @52
    nnmulcl
    syl2an
    nnzd
    @48
    cc0
    @53
    elfz5
    syl2anc
    mpbird
    cc0
    @53
    @48
    fzosplit
    syl
    @54
    cfn
    wcel
    @62
    cc0
    @53
    fzofi
    a1i
    @62
    @3
    @54
    wcel
    #
    wa
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
    @35
    @61
    @76
    dchrisum.b
    ad2antrr
    @76
    @36
    @62
    @3
    cc0
    @53
    elfzoelz
    adantl
    dchrzrhcl
    fsumsplit
    @62
    @66
    cc0
    cc0
    caddc
    co
    cc0
    @62
    @64
    cc0
    cc0
    caddc
    @62
    @64
    @48
    @48
    cN
    caddc
    co
    #
    cfzo
    co
    #
    @5
    vn
    csu
    #
    cc0
    cN
    cfzo
    co
    #
    @5
    vn
    csu
    #
    cc0
    @62
    @63
    @78
    @5
    vn
    @62
    @53
    @77
    @48
    cfzo
    @62
    @53
    @48
    cN
    c1
    cmul
    co
    #
    caddc
    co
    @77
    @62
    cN
    @47
    c1
    @62
    cN
    @73
    nncnd
    #
    @62
    @47
    @71
    recnd
    @62
    1cnd
    adddid
    @62
    @82
    cN
    @48
    caddc
    @62
    cN
    @83
    mulid1d
    oveq2d
    eqtrd
    oveq2d
    sumeq1d
    @62
    @21
    @48
    @48
    @38
    caddc
    co
    #
    cfzo
    co
    #
    @5
    vn
    csu
    #
    cc0
    @38
    cfzo
    co
    #
    @5
    vn
    csu
    #
    wceq
    #
    vk
    cn0
    wral
    #
    @79
    @81
    wceq
    #
    @62
    cN
    @73
    nnnn0d
    #
    @62
    @89
    vk
    cn0
    @62
    @38
    cn0
    wcel
    #
    wa
    #
    @86
    @87
    vi
    cv
    #
    @48
    caddc
    co
    #
    cL
    cfv
    #
    cX
    cfv
    #
    vi
    csu
    #
    @88
    @94
    @48
    @84
    c1
    cmin
    co
    #
    cfz
    co
    #
    @5
    vn
    csu
    @48
    @48
    cmin
    co
    #
    @100
    @48
    cmin
    co
    #
    cfz
    co
    #
    @98
    vi
    csu
    @86
    @99
    @94
    @5
    @98
    vn
    vi
    @48
    @48
    @100
    @62
    @48
    cz
    wcel
    #
    @93
    @62
    @48
    @75
    nn0zd
    #
    adantr
    #
    @107
    @94
    @84
    cz
    wcel
    #
    @100
    cz
    wcel
    @62
    @105
    @38
    cz
    wcel
    #
    @108
    @93
    @106
    @38
    nn0z
    #
    @48
    @38
    zaddcl
    syl2an
    #
    @84
    peano2zm
    syl
    @94
    @3
    @101
    wcel
    #
    wa
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
    @35
    @61
    @93
    @112
    dchrisum.b
    ad3antrrr
    @112
    @36
    @94
    @3
    @48
    @100
    elfzelz
    adantl
    dchrzrhcl
    @3
    @96
    wceq
    @4
    @97
    cX
    @3
    @96
    cL
    fveq2
    fveq2d
    fsumshftm
    @94
    @85
    @101
    @5
    vn
    @94
    @108
    @85
    @101
    wceq
    @111
    @48
    @84
    fzoval
    syl
    sumeq1d
    @94
    @87
    @104
    @98
    vi
    @94
    @87
    cc0
    @38
    c1
    cmin
    co
    #
    cfz
    co
    #
    @104
    @94
    @109
    @87
    @114
    wceq
    @93
    @109
    @62
    @110
    adantl
    cc0
    @38
    fzoval
    syl
    @94
    @102
    cc0
    @103
    @113
    cfz
    @94
    @48
    @94
    @48
    @107
    zcnd
    #
    subidd
    @94
    @103
    @84
    @48
    cmin
    co
    #
    c1
    cmin
    co
    @113
    @94
    @84
    c1
    @48
    @94
    @84
    @111
    zcnd
    @94
    1cnd
    @115
    sub32d
    @94
    @116
    @38
    c1
    cmin
    @94
    @48
    @38
    @115
    @93
    @38
    cc
    wcel
    @62
    @38
    nn0cn
    adantl
    pncan2d
    oveq1d
    eqtrd
    oveq12d
    eqtr4d
    sumeq1d
    3eqtr4d
    @94
    @99
    @87
    @95
    cL
    cfv
    #
    cX
    cfv
    #
    vi
    csu
    @88
    @94
    @87
    @98
    @118
    vi
    @94
    @95
    @87
    wcel
    #
    wa
    #
    @97
    @117
    cX
    @120
    @97
    @117
    wceq
    #
    cN
    @96
    @95
    cmin
    co
    #
    cdvds
    wbr
    #
    @120
    cN
    @48
    @122
    cdvds
    @62
    cN
    @48
    cdvds
    wbr
    #
    @93
    @119
    wph
    cN
    cz
    wcel
    @47
    cz
    wcel
    @124
    @61
    wph
    cN
    rpvmasum.a
    nnzd
    @47
    nn0z
    cN
    @47
    dvdsmul1
    syl2an
    ad2antrr
    @120
    @95
    @48
    @120
    @95
    @119
    @95
    cz
    wcel
    #
    @94
    @95
    cc0
    @38
    elfzoelz
    #
    adantl
    #
    zcnd
    @94
    @48
    cc
    wcel
    @119
    @115
    adantr
    pncan2d
    breqtrrd
    @120
    @21
    @96
    cz
    wcel
    #
    @125
    @121
    @123
    wb
    @62
    @21
    @93
    @119
    @92
    ad2antrr
    @119
    @125
    @105
    @128
    @94
    @126
    @107
    @95
    @48
    zaddcl
    syl2anr
    @127
    @96
    @95
    cL
    cN
    cZ
    rpvmasum.z
    rpvmasum.l
    zndvds
    syl3anc
    mpbird
    fveq2d
    sumeq2dv
    @87
    @118
    @5
    vi
    vn
    vi
    vn
    weq
    @117
    @4
    cX
    @95
    @3
    cL
    fveq2
    fveq2d
    cbvsumv
    syl6eq
    eqtrd
    ralrimiva
    #
    @89
    @91
    vk
    cN
    cn0
    @38
    cN
    wceq
    #
    @86
    @79
    @88
    @81
    @130
    @85
    @78
    @5
    vn
    @130
    @84
    @77
    @48
    cfzo
    @38
    cN
    @48
    caddc
    oveq2
    oveq2d
    sumeq1d
    @130
    @87
    @80
    @5
    vn
    @38
    cN
    cc0
    cfzo
    oveq2
    sumeq1d
    eqeq12d
    rspcv
    sylc
    wph
    @81
    cc0
    wceq
    @61
    wph
    cZ
    cbs
    cfv
    #
    @38
    cX
    cfv
    #
    vk
    csu
    #
    cN
    cc0
    wceq
    cz
    @80
    cif
    #
    @5
    vn
    csu
    cc0
    @81
    wph
    @131
    @132
    @134
    @5
    vk
    vn
    cL
    @134
    cres
    #
    @4
    @38
    @4
    cX
    fveq2
    wph
    @134
    @80
    cfn
    wph
    cN
    cc0
    wne
    @134
    @80
    wceq
    wph
    cN
    rpvmasum.a
    nnne0d
    cN
    cc0
    cz
    @80
    ifnefalse
    syl
    #
    cc0
    cN
    fzofi
    syl6eqel
    wph
    @21
    @134
    @131
    @135
    wf1o
    @22
    @131
    @135
    cN
    @134
    cZ
    rpvmasum.z
    @131
    eqid
    #
    cL
    cZ
    czrh
    cfv
    @134
    rpvmasum.l
    reseq1i
    @134
    eqid
    znf1o
    syl
    @3
    @134
    wcel
    @3
    @135
    cfv
    @4
    wceq
    wph
    @3
    @134
    cL
    fvres
    adantl
    wph
    @131
    cc
    @38
    cX
    wph
    @131
    cD
    cG
    cN
    cX
    cZ
    rpvmasum.g
    rpvmasum.z
    rpvmasum.d
    @137
    dchrisum.b
    dchrf
    ffvelrnda
    fsumf1o
    wph
    @133
    cX
    c.1
    wceq
    cN
    cphi
    cfv
    #
    cc0
    cif
    #
    cc0
    wph
    @131
    cD
    c.1
    cG
    cN
    cX
    cZ
    vk
    rpvmasum.g
    rpvmasum.z
    rpvmasum.d
    rpvmasum.1
    dchrisum.b
    @137
    dchrsum
    wph
    cX
    c.1
    wne
    @139
    cc0
    wceq
    dchrisum.n1
    cX
    c.1
    @138
    cc0
    ifnefalse
    syl
    eqtrd
    wph
    @134
    @80
    @5
    vn
    @136
    sumeq1d
    3eqtr3rd
    adantr
    3eqtrd
    oveq2d
    00id
    syl6req
    eqeq12d
    syl5ibr
    expcom
    a2d
    nn0ind
    impcom
    syldan
    @1
    @17
    @13
    @13
    @7
    caddc
    co
    #
    cfzo
    co
    #
    @5
    vn
    csu
    #
    @9
    @1
    @16
    @141
    @5
    vn
    @1
    cU
    @140
    @13
    cfzo
    @1
    @140
    @13
    cU
    @13
    cmin
    co
    #
    caddc
    co
    cU
    @1
    @7
    @143
    @13
    caddc
    @1
    @25
    cN
    crp
    wcel
    @7
    @143
    wceq
    @26
    @30
    cU
    cN
    modval
    syl2anc
    oveq2d
    @1
    @13
    cU
    @1
    @13
    @32
    nn0cnd
    @0
    cU
    cc
    wcel
    wph
    cU
    nn0cn
    adantl
    pncan3d
    eqtr2d
    oveq2d
    sumeq1d
    @1
    @24
    @7
    cn0
    wcel
    #
    @90
    vm
    cn0
    wral
    #
    @142
    @9
    wceq
    #
    @31
    @0
    cU
    cz
    wcel
    #
    @27
    @144
    wph
    cU
    nn0z
    #
    rpvmasum.a
    cU
    cN
    zmodcl
    syl2anr
    wph
    @145
    @0
    wph
    @90
    vm
    cn0
    @129
    ralrimiva
    adantr
    @89
    @146
    @13
    @13
    @38
    caddc
    co
    #
    cfzo
    co
    #
    @5
    vn
    csu
    #
    @88
    wceq
    vm
    vk
    @12
    @7
    cn0
    cn0
    @47
    @12
    wceq
    #
    @86
    @151
    @88
    @152
    @85
    @150
    @5
    vn
    @152
    @48
    @13
    @84
    @149
    cfzo
    @47
    @12
    cN
    cmul
    oveq2
    #
    @152
    @48
    @13
    @38
    caddc
    @153
    oveq1d
    oveq12d
    sumeq1d
    eqeq1d
    @38
    @7
    wceq
    #
    @151
    @142
    @88
    @9
    @154
    @150
    @141
    @5
    vn
    @154
    @149
    @140
    @13
    cfzo
    @38
    @7
    @13
    caddc
    oveq2
    oveq2d
    sumeq1d
    @154
    @87
    @8
    @5
    vn
    @38
    @7
    cc0
    cfzo
    oveq2
    sumeq1d
    eqeq12d
    rspc2va
    syl21anc
    eqtrd
    oveq12d
    @1
    @9
    @1
    @8
    @5
    vn
    @8
    cfn
    wcel
    @1
    cc0
    @7
    fzofi
    a1i
    @1
    @3
    @8
    wcel
    #
    wa
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
    @35
    @0
    @155
    dchrisum.b
    ad2antrr
    @155
    @36
    @1
    @3
    cc0
    @7
    elfzoelz
    adantl
    dchrzrhcl
    fsumcl
    addid2d
    3eqtrd
    fveq2d
    @1
    @7
    @80
    wcel
    #
    cc0
    vu
    cv
    #
    cfzo
    co
    #
    @5
    vn
    csu
    #
    cabs
    cfv
    #
    cR
    cle
    wbr
    #
    vu
    @80
    wral
    #
    @10
    cR
    cle
    wbr
    #
    @0
    @147
    @27
    @156
    wph
    @148
    rpvmasum.a
    cU
    cN
    zmodfzo
    syl2anr
    wph
    @162
    @0
    dchrisum.10
    adantr
    @161
    @163
    vu
    @7
    @80
    @157
    @7
    wceq
    #
    @160
    @10
    cR
    cle
    @164
    @159
    @9
    cabs
    @164
    @158
    @8
    @5
    vn
    @157
    @7
    cc0
    cfzo
    oveq2
    sumeq1d
    fveq2d
    breq1d
    rspcv
    sylc
    eqbrtrd
end
