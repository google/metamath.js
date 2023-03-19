include "caddc.mm"
include "c1.mm"
include "cseq.mm"
include "cv.mm"
include "cli.mm"
include "wbr.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "csqrt.mm"
include "cdiv.mm"
include "cle.mm"
include "cpnf.mm"
include "cico.mm"
include "wral.mm"
include "wa.mm"
include "cc0.mm"
include "wrex.mm"
include "wex.mm"
include "cn.mm"
include "cmul.mm"
include "cmpt.mm"
include "csn.mm"
include "cdif.mm"
include "csu.mm"
include "wceq.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "eldifad.mm"
include "wcel.mm"
include "wne.mm"
include "eldifsni.mm"
include "syl.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "1nn.mm"
include "a1i.mm"
include "crp.mm"
include "rpsqrtcl.mm"
include "adantl.mm"
include "rprecred.mm"
include "w3a.mm"
include "simp3r.mm"
include "cr.mm"
include "wb.mm"
include "simp2l.mm"
include "rprege0d.mm"
include "simp2r.mm"
include "sqrtle.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "rpsqrtcld.mm"
include "lerecd.mm"
include "crli.mm"
include "sqrtlim.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "dchrisum.mm"
include "adantr.mm"
include "cz.mm"
include "nnz.mm"
include "dchrzrhcl.mm"
include "simpr.mm"
include "nnrpd.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divrecd.mm"
include "mpteq2dva.mm"
include "eqtri.mm"
include "3eqtr4g.mm"
include "seqeq3d.mm"
include "breq1d.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "cbvralv.mm"
include "ad2antrr.mm"
include "fveq1d.mm"
include "elrege0.mm"
include "simplbi.mm"
include "ad2antlr.mm"
include "recnd.mm"
include "1re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "0red.mm"
include "1red.mm"
include "clt.mm"
include "0lt1.mm"
include "simprbi.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "rexbidva.mm"
include "exbidv.mm"
include "mpbird.mm"

theorem dchrisum0lema
  let wph: wff ph
  let vy: setvar y
  let vt: setvar t
  let cD: class D
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
  let vc: setvar c
  let vk: setvar k
  let vn: setvar n
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vp: setvar p
  let vd: setvar d
  let cC: class C
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
  assume dchrisum0lem1.f: |- F = ( a e. NN |-> ( ( X ` ( L ` a ) ) / ( sqrt ` a ) ) )

  disjoint F m
  disjoint m y
  disjoint c m
  disjoint c t
  disjoint c y
  disjoint .1. c
  disjoint m t
  disjoint .1. m
  disjoint t y
  disjoint .1. t
  disjoint .1. y
  disjoint F c
  disjoint F t
  disjoint F y
  disjoint a c
  disjoint a m
  disjoint a t
  disjoint a y
  disjoint N c
  disjoint N m
  disjoint N t
  disjoint N y
  disjoint c ph
  disjoint m ph
  disjoint ph t
  disjoint W c
  disjoint W t
  disjoint Z m
  disjoint Z y
  disjoint D c
  disjoint D m
  disjoint D t
  disjoint D y
  disjoint L a
  disjoint L c
  disjoint L m
  disjoint L t
  disjoint L y
  disjoint X a
  disjoint X c
  disjoint X m
  disjoint X t
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
  disjoint c n
  disjoint c p
  disjoint c x
  disjoint c z
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
  disjoint n p
  disjoint n t
  disjoint .1. n
  disjoint p t
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint .1. p
  disjoint t x
  disjoint t z
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
  disjoint F u
  disjoint F x
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
  disjoint a d
  disjoint a f
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a p
  disjoint a q
  disjoint a v
  disjoint a x
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
  disjoint W f
  disjoint W x
  disjoint W z
  disjoint Z f
  disjoint Z k
  disjoint Z n
  disjoint Z p
  disjoint Z x
  disjoint Z z
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D k
  disjoint D n
  disjoint D x
  disjoint D z
  disjoint a n
  disjoint a r
  disjoint a u
  disjoint b u
  disjoint L b
  disjoint L d
  disjoint L f
  disjoint L i
  disjoint L j
  disjoint L k
  disjoint L n
  disjoint L p
  disjoint L r
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
  disjoint X b
  disjoint X d
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X n
  disjoint X r
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X z
  assert |- ( ph -> E. t E. c e. ( 0 [,) +oo ) ( seq 1 ( + , F ) ~~> t /\ A. y e. ( 1 [,) +oo ) ( abs ` ( ( seq 1 ( + , F ) ` ( |_ ` y ) ) - t ) ) <_ ( c / ( sqrt ` y ) ) ) )

  proof
    wph
    caddc
    cF
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
    @0
    cfv
    #
    @1
    cmin
    co
    #
    cabs
    cfv
    #
    vc
    cv
    #
    @3
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
    caddc
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
    c1
    @17
    csqrt
    cfv
    #
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    #
    c1
    cseq
    #
    @1
    cli
    wbr
    #
    vx
    cv
    #
    cfl
    cfv
    #
    @24
    cfv
    #
    @1
    cmin
    co
    #
    cabs
    cfv
    #
    @8
    c1
    @26
    csqrt
    cfv
    #
    cdiv
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    vx
    @12
    wral
    #
    wa
    #
    vc
    @15
    wrex
    #
    vt
    wex
    wph
    vx
    vt
    c1
    vn
    cv
    #
    csqrt
    cfv
    #
    cdiv
    co
    #
    @32
    cD
    c.1
    vn
    @23
    cG
    cL
    c1
    cN
    cX
    cZ
    vc
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    rpvmasum2.g
    rpvmasum2.d
    rpvmasum2.1
    wph
    cX
    cD
    c.1
    csn
    #
    wph
    cW
    cD
    @41
    cdif
    #
    cX
    cW
    cn
    vm
    cv
    #
    cL
    cfv
    @3
    cfv
    @43
    cdiv
    co
    vm
    csu
    cc0
    wceq
    #
    vy
    @42
    crab
    @42
    rpvmasum2.w
    @44
    vy
    @42
    ssrab2
    eqsstri
    dchrisum0.b
    sseldi
    #
    eldifad
    #
    wph
    cX
    @42
    wcel
    cX
    c.1
    wne
    @45
    cX
    cD
    c.1
    eldifsni
    syl
    vn
    vx
    weq
    @39
    @31
    c1
    cdiv
    @38
    @26
    csqrt
    fveq2
    oveq2d
    c1
    cn
    wcel
    wph
    1nn
    a1i
    wph
    @38
    crp
    wcel
    #
    wa
    @39
    @47
    @39
    crp
    wcel
    wph
    @38
    rpsqrtcl
    adantl
    rprecred
    wph
    @47
    @26
    crp
    wcel
    #
    wa
    #
    c1
    @38
    cle
    wbr
    #
    @38
    @26
    cle
    wbr
    #
    wa
    #
    w3a
    #
    @39
    @31
    cle
    wbr
    #
    @32
    @40
    cle
    wbr
    @53
    @51
    @54
    wph
    @49
    @50
    @51
    simp3r
    @53
    @38
    cr
    wcel
    cc0
    @38
    cle
    wbr
    wa
    @26
    cr
    wcel
    #
    cc0
    @26
    cle
    wbr
    wa
    @51
    @54
    wb
    @53
    @38
    wph
    @47
    @48
    @52
    simp2l
    #
    rprege0d
    @53
    @26
    wph
    @47
    @48
    @52
    simp2r
    #
    rprege0d
    @38
    @26
    sqrtle
    syl2anc
    mpbid
    @53
    @39
    @31
    @53
    @38
    @56
    rpsqrtcld
    @53
    @26
    @57
    rpsqrtcld
    lerecd
    mpbid
    vn
    crp
    @40
    cmpt
    cc0
    crli
    wbr
    wph
    vn
    sqrtlim
    a1i
    va
    vn
    cn
    @22
    @38
    cL
    cfv
    #
    cX
    cfv
    #
    @40
    cmul
    co
    #
    va
    vn
    weq
    #
    @19
    @59
    @21
    @40
    cmul
    @61
    @18
    @58
    cX
    @17
    @38
    cL
    fveq2
    fveq2d
    #
    @61
    @20
    @39
    c1
    cdiv
    @17
    @38
    csqrt
    fveq2
    #
    oveq2d
    oveq12d
    cbvmptv
    #
    dchrisum
    wph
    @16
    @37
    vt
    wph
    @14
    @36
    vc
    @15
    wph
    @8
    @15
    wcel
    #
    wa
    #
    @2
    @25
    @13
    @35
    wph
    @2
    @25
    wb
    @65
    wph
    @0
    @24
    @1
    cli
    wph
    cF
    @23
    caddc
    c1
    wph
    vn
    cn
    @59
    @39
    cdiv
    co
    #
    cmpt
    #
    vn
    cn
    @60
    cmpt
    cF
    @23
    wph
    vn
    cn
    @67
    @60
    wph
    @38
    cn
    wcel
    #
    wa
    #
    @59
    @39
    @70
    @38
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
    @69
    @46
    adantr
    @69
    @38
    cz
    wcel
    wph
    @38
    nnz
    adantl
    dchrzrhcl
    @70
    @39
    @70
    @38
    @70
    @38
    wph
    @69
    simpr
    nnrpd
    rpsqrtcld
    #
    rpcnd
    @70
    @39
    @71
    rpne0d
    divrecd
    mpteq2dva
    cF
    va
    cn
    @19
    @20
    cdiv
    co
    #
    cmpt
    @68
    dchrisum0lem1.f
    va
    vn
    cn
    @72
    @67
    @61
    @19
    @59
    @20
    @39
    cdiv
    @62
    @63
    oveq12d
    cbvmptv
    eqtri
    @64
    3eqtr4g
    #
    seqeq3d
    breq1d
    adantr
    @13
    @27
    @0
    cfv
    #
    @1
    cmin
    co
    #
    cabs
    cfv
    #
    @8
    @31
    cdiv
    co
    #
    cle
    wbr
    #
    vx
    @12
    wral
    @66
    @35
    @11
    @78
    vy
    vx
    @12
    vy
    vx
    weq
    #
    @7
    @76
    @10
    @77
    cle
    @79
    @6
    @75
    cabs
    @79
    @5
    @74
    @1
    cmin
    @79
    @4
    @27
    @0
    @3
    @26
    cfl
    fveq2
    fveq2d
    oveq1d
    fveq2d
    @79
    @9
    @31
    @8
    cdiv
    @3
    @26
    csqrt
    fveq2
    oveq2d
    breq12d
    cbvralv
    @66
    @78
    @34
    vx
    @12
    @66
    @26
    @12
    wcel
    #
    wa
    #
    @76
    @30
    @77
    @33
    cle
    @81
    @75
    @29
    cabs
    @81
    @74
    @28
    @1
    cmin
    @81
    @27
    @0
    @24
    @81
    cF
    @23
    caddc
    c1
    wph
    cF
    @23
    wceq
    @65
    @80
    @73
    ad2antrr
    seqeq3d
    fveq1d
    oveq1d
    fveq2d
    @81
    @8
    @31
    @81
    @8
    @65
    @8
    cr
    wcel
    #
    wph
    @80
    @65
    @82
    cc0
    @8
    cle
    wbr
    @8
    elrege0
    simplbi
    ad2antlr
    recnd
    @81
    @31
    @81
    @26
    @81
    @26
    @80
    @55
    @66
    @80
    @55
    c1
    @26
    cle
    wbr
    #
    c1
    cr
    wcel
    @80
    @55
    @83
    wa
    wb
    1re
    c1
    @26
    elicopnf
    ax-mp
    #
    simplbi
    adantl
    #
    @81
    cc0
    c1
    @26
    @81
    0red
    @81
    1red
    @85
    cc0
    c1
    clt
    wbr
    @81
    0lt1
    a1i
    @80
    @83
    @66
    @80
    @55
    @83
    @84
    simprbi
    adantl
    ltletrd
    elrpd
    rpsqrtcld
    #
    rpcnd
    @81
    @31
    @86
    rpne0d
    divrecd
    breq12d
    ralbidva
    syl5bb
    anbi12d
    rexbidva
    exbidv
    mpbird
end
