include "cn.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cfv.mm"
include "csu.mm"
include "cmpt.mm"
include "eqid.mm"
include "csn.mm"
include "cdif.mm"
include "cdiv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "difss.mm"
include "sstri.mm"
include "sseldi.mm"
include "dchrisum0re.mm"
include "crp.mm"
include "c1.mm"
include "cfl.mm"
include "cfz.mm"
include "csqrt.mm"
include "c2.mm"
include "cexp.mm"
include "cmul.mm"
include "ccom.mm"
include "co1.mm"
include "wcel.mm"
include "wa.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "cr.mm"
include "rpre.mm"
include "adantl.mm"
include "cc.mm"
include "ad3antrrr.mm"
include "cz.mm"
include "elrabi.mm"
include "nnzd.mm"
include "dchrzrhcl.mm"
include "elfznn.mm"
include "nnrpd.mm"
include "rpsqrtcld.mm"
include "rpcnd.mm"
include "adantr.mm"
include "wne.mm"
include "rpne0d.mm"
include "divcld.mm"
include "anasss.mm"
include "dvdsflsumcom.mm"
include "dchrisum0fval.mm"
include "syl.mm"
include "oveq1d.mm"
include "cfn.mm"
include "wss.mm"
include "fzfid.mm"
include "dvdsssfz1.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "fsumdivc.mm"
include "eqtrd.mm"
include "sumeq2dv.mm"
include "cle.mm"
include "rprege0.mm"
include "resqrtth.mm"
include "fveq2d.mm"
include "sumeq1d.mm"
include "sumeq12dv.mm"
include "3eqtr4d.mm"
include "mpteq2dva.mm"
include "rpsqrtcl.mm"
include "eqidd.mm"
include "oveq1.mm"
include "fmptco.mm"
include "eqtr4d.mm"
include "cdm.mm"
include "wf.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cmin.mm"
include "cabs.mm"
include "cpnf.mm"
include "cico.mm"
include "wral.mm"
include "wrex.mm"
include "wex.mm"
include "dchrisum0lema.mm"
include "simprl.mm"
include "simprrl.mm"
include "simprrr.mm"
include "dchrisum0lem3.mm"
include "rexlimdvaa.mm"
include "exlimdv.mm"
include "mpd.mm"
include "o1f.mm"
include "sumex.mm"
include "dmmpti.mm"
include "feq2i.mm"
include "sylib.mm"
include "rpssre.mm"
include "a1i.mm"
include "wi.mm"
include "resqcl.mm"
include "0red.mm"
include "simplr.mm"
include "simplrr.mm"
include "ad2antrl.mm"
include "breqtrrd.mm"
include "rpred.mm"
include "ad2ant2r.mm"
include "simpr.mm"
include "sqrtge0.mm"
include "le2sqd.mm"
include "mpbird.mm"
include "letrd.mm"
include "lecasei.mm"
include "expr.mm"
include "ralrimiva.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "o1compt.mm"
include "eqeltrd.mm"
include "dchrisum0fno1.mm"

theorem dchrisum0
  let wph: wff ph
  let vy: setvar y
  let cD: class D
  let c.1: class .1.
  let vm: setvar m
  let cG: class G
  let cL: class L
  let cN: class N
  let cW: class W
  let cX: class X
  let cZ: class Z
  let vk: setvar k
  let vn: setvar n
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
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
  let cF: class F
  let cI: class I
  let cJ: class J
  let va: setvar a
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
  let cS: class S
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

  disjoint m y
  disjoint .1. m
  disjoint .1. y
  disjoint N m
  disjoint N y
  disjoint m ph
  disjoint Z m
  disjoint Z y
  disjoint D m
  disjoint D y
  disjoint L m
  disjoint L y
  disjoint X m
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
  disjoint m x
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
  disjoint .1. x
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
  disjoint F x
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
  disjoint N x
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
  disjoint n ph
  disjoint p ph
  disjoint ph r
  disjoint ph t
  disjoint ph u
  disjoint ph x
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
  disjoint Z n
  disjoint Z p
  disjoint Z x
  disjoint Z z
  disjoint D c
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D k
  disjoint D n
  disjoint D t
  disjoint D x
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
  disjoint L n
  disjoint L p
  disjoint L r
  disjoint L t
  disjoint u v
  disjoint L u
  disjoint L v
  disjoint L x
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
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X n
  disjoint X r
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X z
  assert |- -. ph

  proof
    wph
    vx
    vy
    cD
    c.1
    vk
    vb
    cn
    vi
    cv
    #
    vb
    cv
    cdvds
    wbr
    vi
    cn
    crab
    vy
    cv
    #
    cL
    cfv
    cX
    cfv
    vy
    csu
    cmpt
    #
    cG
    cL
    cN
    cX
    cZ
    vi
    vb
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    rpvmasum2.g
    rpvmasum2.d
    rpvmasum2.1
    @2
    eqid
    #
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
    vm
    cv
    #
    cL
    cfv
    #
    @1
    cfv
    @6
    cdiv
    co
    vm
    csu
    cc0
    wceq
    #
    vy
    @5
    crab
    @5
    rpvmasum2.w
    @8
    vy
    @5
    ssrab2
    eqsstri
    cD
    @4
    difss
    sstri
    dchrisum0.b
    sseldi
    #
    wph
    vy
    cD
    c.1
    vm
    cG
    cL
    cN
    cW
    cX
    cZ
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    rpvmasum2.g
    rpvmasum2.d
    rpvmasum2.1
    rpvmasum2.w
    dchrisum0.b
    dchrisum0re
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
    vk
    cv
    #
    @2
    cfv
    #
    @13
    csqrt
    cfv
    #
    cdiv
    co
    #
    vk
    csu
    #
    cmpt
    #
    vz
    crp
    c1
    vz
    cv
    #
    c2
    cexp
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    c1
    @20
    @6
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    @7
    cX
    cfv
    #
    @6
    vd
    cv
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
    cmpt
    #
    vx
    crp
    @10
    csqrt
    cfv
    #
    cmpt
    #
    ccom
    #
    co1
    wph
    @18
    vx
    crp
    c1
    @33
    c2
    cexp
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    c1
    @36
    @6
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    @29
    vd
    csu
    #
    vm
    csu
    #
    cmpt
    @35
    wph
    vx
    crp
    @17
    @43
    wph
    @10
    crp
    wcel
    #
    wa
    #
    @12
    @0
    @13
    cdvds
    wbr
    #
    vi
    cn
    crab
    #
    @26
    @15
    cdiv
    co
    #
    vm
    csu
    #
    vk
    csu
    @12
    c1
    @10
    @6
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    @29
    vd
    csu
    #
    vm
    csu
    @17
    @43
    @45
    vi
    @10
    @48
    @29
    vd
    vk
    vm
    @13
    @27
    wceq
    @15
    @28
    @26
    cdiv
    @13
    @27
    csqrt
    fveq2
    oveq2d
    @44
    @10
    cr
    wcel
    #
    wph
    @10
    rpre
    adantl
    @45
    @13
    @12
    wcel
    #
    @6
    @47
    wcel
    #
    @48
    cc
    wcel
    @45
    @55
    wa
    #
    @56
    wa
    #
    @26
    @15
    @58
    @6
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
    @44
    @55
    @56
    @9
    ad3antrrr
    @56
    @6
    cz
    wcel
    @57
    @56
    @6
    @46
    vi
    @6
    cn
    elrabi
    nnzd
    adantl
    dchrzrhcl
    #
    @57
    @15
    cc
    wcel
    @56
    @57
    @15
    @57
    @13
    @57
    @13
    @55
    @13
    cn
    wcel
    #
    @45
    @13
    @11
    elfznn
    adantl
    #
    nnrpd
    rpsqrtcld
    #
    rpcnd
    #
    adantr
    @57
    @15
    cc0
    wne
    @56
    @57
    @15
    @62
    rpne0d
    #
    adantr
    divcld
    anasss
    dvdsflsumcom
    @45
    @12
    @16
    @49
    vk
    @57
    @16
    @47
    @26
    vm
    csu
    #
    @15
    cdiv
    co
    @49
    @57
    @14
    @65
    @15
    cdiv
    @57
    @60
    @14
    @65
    wceq
    @61
    wph
    vy
    vm
    @13
    cD
    c.1
    @2
    cG
    cL
    cN
    cX
    cZ
    vi
    vb
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    rpvmasum2.g
    rpvmasum2.d
    rpvmasum2.1
    @3
    dchrisum0fval
    syl
    oveq1d
    @57
    @47
    @26
    @15
    vm
    @57
    c1
    @13
    cfz
    co
    #
    cfn
    wcel
    @47
    @66
    wss
    #
    @47
    cfn
    wcel
    @57
    c1
    @13
    fzfid
    @57
    @60
    @67
    @61
    @13
    vi
    dvdsssfz1
    syl
    @66
    @47
    ssfi
    syl2anc
    @63
    @59
    @64
    fsumdivc
    eqtrd
    sumeq2dv
    @45
    @38
    @12
    @42
    @53
    vm
    @45
    @37
    @11
    c1
    cfz
    @45
    @36
    @10
    cfl
    @45
    @54
    cc0
    @10
    cle
    wbr
    wa
    #
    @36
    @10
    wceq
    #
    @44
    @68
    wph
    @10
    rprege0
    #
    adantl
    @10
    resqrtth
    #
    syl
    #
    fveq2d
    oveq2d
    @45
    @42
    @53
    wceq
    @6
    @38
    wcel
    @45
    @41
    @52
    @29
    vd
    @45
    @40
    @51
    c1
    cfz
    @45
    @39
    @50
    cfl
    @45
    @36
    @10
    @6
    cdiv
    @72
    oveq1d
    fveq2d
    oveq2d
    sumeq1d
    adantr
    sumeq12dv
    3eqtr4d
    mpteq2dva
    wph
    vx
    vz
    crp
    crp
    @33
    @31
    @43
    @34
    @32
    @44
    @33
    crp
    wcel
    wph
    @10
    rpsqrtcl
    adantl
    #
    wph
    @34
    eqidd
    wph
    @32
    eqidd
    @19
    @33
    wceq
    #
    @22
    @38
    @30
    @42
    vm
    @74
    @21
    @37
    c1
    cfz
    @74
    @20
    @36
    cfl
    @19
    @33
    c2
    cexp
    oveq1
    #
    fveq2d
    oveq2d
    @74
    @30
    @42
    wceq
    @6
    @22
    wcel
    @74
    @25
    @41
    @29
    vd
    @74
    @24
    @40
    c1
    cfz
    @74
    @23
    @39
    cfl
    @74
    @20
    @36
    @6
    cdiv
    @75
    oveq1d
    fveq2d
    oveq2d
    sumeq1d
    adantr
    sumeq12dv
    fmptco
    eqtr4d
    wph
    vc
    vx
    crp
    crp
    @33
    vt
    @32
    wph
    @32
    cdm
    #
    cc
    @32
    wf
    #
    crp
    cc
    @32
    wf
    wph
    @32
    co1
    wcel
    #
    @77
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
    @79
    csqrt
    cfv
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
    @1
    cfl
    cfv
    @81
    cfv
    @82
    cmin
    co
    cabs
    cfv
    vc
    cv
    #
    @1
    csqrt
    cfv
    cdiv
    co
    cle
    wbr
    vy
    c1
    cpnf
    cico
    co
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
    @78
    wph
    vy
    vt
    cD
    c.1
    vm
    @80
    cG
    cL
    cN
    cW
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
    rpvmasum2.w
    dchrisum0.b
    @80
    eqid
    #
    dchrisum0lema
    wph
    @88
    @78
    vt
    wph
    @86
    @78
    vc
    @87
    wph
    @84
    @87
    wcel
    #
    @86
    wa
    #
    wa
    vz
    vy
    @84
    cD
    @82
    c.1
    vm
    @80
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
    wph
    cN
    cn
    wcel
    @91
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
    @91
    dchrisum0.b
    adantr
    @89
    wph
    @90
    @86
    simprl
    wph
    @90
    @83
    @85
    simprrl
    wph
    @90
    @83
    @85
    simprrr
    dchrisum0lem3
    rexlimdvaa
    exlimdv
    mpd
    #
    @32
    o1f
    syl
    @76
    crp
    cc
    @32
    vz
    crp
    @31
    @32
    @22
    @30
    vm
    sumex
    @32
    eqid
    dmmpti
    feq2i
    sylib
    @92
    @73
    crp
    cr
    wss
    wph
    rpssre
    a1i
    wph
    @82
    cr
    wcel
    #
    wa
    #
    @82
    c2
    cexp
    co
    #
    cr
    wcel
    #
    @95
    @10
    cle
    wbr
    #
    @82
    @33
    cle
    wbr
    #
    wi
    #
    vx
    crp
    wral
    #
    @84
    @10
    cle
    wbr
    #
    @98
    wi
    #
    vx
    crp
    wral
    #
    vc
    cr
    wrex
    @93
    @96
    wph
    @82
    resqcl
    adantl
    @94
    @99
    vx
    crp
    @94
    @44
    @97
    @98
    @94
    @44
    @97
    wa
    #
    wa
    #
    @98
    cc0
    @82
    @105
    0red
    wph
    @93
    @104
    simplr
    #
    @105
    cc0
    @82
    cle
    wbr
    #
    wa
    #
    @98
    @95
    @36
    cle
    wbr
    @108
    @95
    @10
    @36
    cle
    @94
    @44
    @97
    @107
    simplrr
    @108
    @68
    @69
    @105
    @68
    @107
    @44
    @68
    @94
    @97
    @70
    ad2antrl
    #
    adantr
    @71
    syl
    breqtrrd
    @108
    @82
    @33
    @105
    @93
    @107
    @106
    adantr
    @105
    @33
    cr
    wcel
    #
    @107
    wph
    @44
    @110
    @93
    @97
    @45
    @33
    @73
    rpred
    ad2ant2r
    #
    adantr
    @105
    @107
    simpr
    @105
    cc0
    @33
    cle
    wbr
    #
    @107
    @105
    @68
    @112
    @109
    @10
    sqrtge0
    syl
    #
    adantr
    le2sqd
    mpbird
    @105
    @82
    cc0
    cle
    wbr
    #
    wa
    #
    @82
    cc0
    @33
    @105
    @93
    @114
    @106
    adantr
    @115
    0red
    @105
    @110
    @114
    @111
    adantr
    @105
    @114
    simpr
    @105
    @112
    @114
    @113
    adantr
    letrd
    lecasei
    expr
    ralrimiva
    @103
    @100
    vc
    @95
    cr
    @84
    @95
    wceq
    #
    @102
    @99
    vx
    crp
    @116
    @101
    @97
    @98
    @84
    @95
    @10
    cle
    breq1
    imbi1d
    ralbidv
    rspcev
    syl2anc
    o1compt
    eqeltrd
    dchrisum0fno1
end
