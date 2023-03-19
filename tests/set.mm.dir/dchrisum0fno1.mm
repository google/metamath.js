include "crp.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "logno1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wa.mm"
include "cr.mm"
include "relogcl.mm"
include "adantl.mm"
include "recnd.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divcan2d.mm"
include "mpteq2dva.mm"
include "cc.mm"
include "rehalfcld.mm"
include "wss.mm"
include "rpssre.mm"
include "2cn.mm"
include "o1const.mm"
include "mp2an.mm"
include "c1.mm"
include "cfl.mm"
include "cfz.mm"
include "csqrt.mm"
include "csu.mm"
include "cvv.mm"
include "1red.mm"
include "sumex.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "adantrr.mm"
include "clt.mm"
include "ad2antrl.mm"
include "log1.mm"
include "simprr.mm"
include "wb.mm"
include "1rp.mm"
include "simprl.mm"
include "logleb.mm"
include "sylancr.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "2re.mm"
include "2pos.mm"
include "divge0.mm"
include "syl22anc.mm"
include "absidd.mm"
include "fzfid.mm"
include "cn.mm"
include "wf.mm"
include "dchrisum0ff.mm"
include "adantr.mm"
include "elfznn.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "nnrpd.mm"
include "rpsqrtcld.mm"
include "rerpdivcld.mm"
include "fsumrecl.mm"
include "abscld.mm"
include "nnrecred.mm"
include "wceq.mm"
include "logsqrt.mm"
include "rpsqrtcl.mm"
include "harmoniclbnd.mm"
include "syl.mm"
include "eqbrtrrd.mm"
include "cif.mm"
include "cexp.mm"
include "crn.mm"
include "wrex.mm"
include "eqid.mm"
include "ovex.mm"
include "elrnmpti.mm"
include "rprege0d.mm"
include "sqrtsq.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "imp.mm"
include "iftrued.mm"
include "oveq1d.mm"
include "sumeq2dv.mm"
include "oveq2d.mm"
include "wf1.mm"
include "wf1o.mm"
include "nnsqcld.mm"
include "rpred.mm"
include "fznnfl.mm"
include "simplbda.mm"
include "le2sq.mm"
include "syl2anc.mm"
include "sqsqrtd.mm"
include "breqtrd.mm"
include "mpbir2and.mm"
include "ex.mm"
include "wi.mm"
include "sq11.mm"
include "dom2lem.mm"
include "f1f1orn.mm"
include "oveq1.mm"
include "fvmpt3i.mm"
include "f1f.mm"
include "frn.mm"
include "3syl.mm"
include "sselda.mm"
include "1re.mm"
include "0re.mm"
include "keepel.mm"
include "rerpdivcl.mm"
include "syldan.mm"
include "eqeltrrd.mm"
include "fsumf1o.mm"
include "eqtrd.mm"
include "cdif.mm"
include "wn.mm"
include "eldif.mm"
include "nncnd.mm"
include "sqrtle.mm"
include "elrnmpt1s.mm"
include "expr.mm"
include "con3d.mm"
include "impr.mm"
include "sylan2b.mm"
include "iffalsed.mm"
include "eldifi.mm"
include "sylan2.mm"
include "rpcnne0d.mm"
include "div0.mm"
include "fsumss.mm"
include "3eqtr3d.mm"
include "ad2antrr.mm"
include "cbs.mm"
include "dchrisum0flb.mm"
include "lediv1dd.mm"
include "fsumle.mm"
include "letrd.mm"
include "leabsd.mm"
include "eqbrtrd.mm"
include "o1le.mm"
include "o1mul2.mm"
include "mto.mm"

theorem dchrisum0fno1
  let wph: wff ph
  let vx: setvar x
  let vv: setvar v
  let cD: class D
  let c.1: class .1.
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cL: class L
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vq: setvar q
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
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
  let cW: class W
  let cM: class M
  assume rpvmasum.z: |- Z = ( Z/nZ ` N )
  assume rpvmasum.l: |- L = ( ZRHom ` Z )
  assume rpvmasum.a: |- ( ph -> N e. NN )
  assume rpvmasum2.g: |- G = ( DChr ` N )
  assume rpvmasum2.d: |- D = ( Base ` G )
  assume rpvmasum2.1: |- .1. = ( 0g ` G )
  assume dchrisum0f.f: |- F = ( b e. NN |-> sum_ v e. { q e. NN | q || b } ( X ` ( L ` v ) ) )
  assume dchrisum0f.x: |- ( ph -> X e. D )
  assume dchrisum0flb.r: |- ( ph -> X : ( Base ` Z ) --> RR )
  assume dchrisum0fno1.a: |- ( ph -> ( x e. RR+ |-> sum_ k e. ( 1 ... ( |_ ` x ) ) ( ( F ` k ) / ( sqrt ` k ) ) ) e. O(1) )

  disjoint k x
  disjoint .1. k
  disjoint .1. x
  disjoint F k
  disjoint F x
  disjoint b k
  disjoint b q
  disjoint b v
  disjoint b x
  disjoint k q
  disjoint k v
  disjoint q v
  disjoint q x
  disjoint v x
  disjoint N k
  disjoint N q
  disjoint N x
  disjoint k ph
  disjoint ph x
  disjoint Z k
  disjoint Z x
  disjoint D k
  disjoint D x
  disjoint L b
  disjoint L k
  disjoint L v
  disjoint L x
  disjoint X b
  disjoint X k
  disjoint X v
  disjoint X x
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k w
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
  disjoint m p
  disjoint m t
  disjoint .1. m
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
  disjoint b m
  disjoint b p
  disjoint b t
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
  disjoint A k
  disjoint m q
  disjoint m v
  disjoint A m
  disjoint p q
  disjoint p v
  disjoint A p
  disjoint q t
  disjoint q y
  disjoint q z
  disjoint A q
  disjoint t v
  disjoint A t
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
  disjoint N m
  disjoint n q
  disjoint N n
  disjoint N p
  disjoint q r
  disjoint q u
  disjoint N r
  disjoint N t
  disjoint N u
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
  disjoint m ph
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
  disjoint Z m
  disjoint Z n
  disjoint Z p
  disjoint Z y
  disjoint Z z
  disjoint D c
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D m
  disjoint D n
  disjoint D t
  disjoint D y
  disjoint D z
  disjoint a n
  disjoint a r
  disjoint a u
  disjoint L a
  disjoint b u
  disjoint L c
  disjoint L d
  disjoint L f
  disjoint L i
  disjoint L j
  disjoint L m
  disjoint L n
  disjoint L p
  disjoint L r
  disjoint L t
  disjoint u v
  disjoint L u
  disjoint L y
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
  disjoint X c
  disjoint X d
  disjoint X i
  disjoint X j
  disjoint X m
  disjoint X n
  disjoint X r
  disjoint X t
  disjoint X u
  disjoint X y
  disjoint X z
  assert |- -. ph

  proof
    wph
    vx
    crp
    vx
    cv
    #
    clog
    cfv
    #
    cmpt
    #
    co1
    wcel
    vx
    logno1
    wph
    vx
    crp
    c2
    @1
    c2
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    @2
    co1
    wph
    vx
    crp
    @4
    @1
    wph
    @0
    crp
    wcel
    #
    wa
    #
    @1
    c2
    @6
    @1
    @5
    @1
    cr
    wcel
    #
    wph
    @0
    relogcl
    #
    adantl
    #
    recnd
    @6
    2cnd
    #
    c2
    cc0
    wne
    @6
    2ne0
    a1i
    divcan2d
    mpteq2dva
    wph
    vx
    crp
    c2
    @3
    cc
    @10
    @6
    @3
    @6
    @1
    @9
    rehalfcld
    #
    recnd
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
    c2
    cc
    wcel
    @13
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
    c1
    @0
    cfl
    cfv
    #
    cfz
    co
    #
    vk
    cv
    #
    cF
    cfv
    #
    @16
    csqrt
    cfv
    #
    cdiv
    co
    #
    vk
    csu
    #
    @3
    c1
    cvv
    wph
    1red
    dchrisum0fno1.a
    @20
    cvv
    wcel
    @6
    @15
    @19
    vk
    sumex
    a1i
    @12
    wph
    @5
    c1
    @0
    cle
    wbr
    #
    wa
    #
    wa
    #
    @3
    cabs
    cfv
    @3
    @20
    cabs
    cfv
    #
    cle
    @23
    @3
    wph
    @5
    @3
    cr
    wcel
    @21
    @11
    adantrr
    #
    @23
    @7
    cc0
    @1
    cle
    wbr
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    cc0
    @3
    cle
    wbr
    @5
    @7
    wph
    @21
    @8
    ad2antrl
    @23
    cc0
    c1
    clog
    cfv
    #
    @1
    cle
    log1
    @23
    @21
    @28
    @1
    cle
    wbr
    #
    wph
    @5
    @21
    simprr
    @23
    c1
    crp
    wcel
    @5
    @21
    @29
    wb
    1rp
    wph
    @5
    @21
    simprl
    #
    c1
    @0
    logleb
    sylancr
    mpbid
    syl5eqbrr
    @26
    @23
    2re
    a1i
    @27
    @23
    2pos
    a1i
    @1
    c2
    divge0
    syl22anc
    absidd
    @23
    @3
    @20
    @24
    @25
    @23
    @15
    @19
    vk
    @23
    c1
    @14
    fzfid
    #
    @23
    @16
    @15
    wcel
    #
    wa
    #
    @17
    @18
    @23
    cn
    cr
    cF
    wf
    #
    @16
    cn
    wcel
    #
    @17
    cr
    wcel
    @32
    wph
    @34
    @22
    wph
    vv
    cD
    c.1
    cF
    cG
    cL
    cN
    cX
    cZ
    vq
    vb
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    rpvmasum2.g
    rpvmasum2.d
    rpvmasum2.1
    dchrisum0f.f
    dchrisum0f.x
    dchrisum0flb.r
    dchrisum0ff
    adantr
    @16
    @14
    elfznn
    #
    cn
    cr
    @16
    cF
    ffvelrn
    syl2an
    #
    @33
    @16
    @33
    @16
    @32
    @35
    @23
    @36
    adantl
    #
    nnrpd
    rpsqrtcld
    #
    rerpdivcld
    #
    fsumrecl
    #
    @23
    @20
    @23
    @20
    @41
    recnd
    abscld
    @23
    @3
    c1
    @0
    csqrt
    cfv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    c1
    vi
    cv
    #
    cdiv
    co
    #
    vi
    csu
    #
    @20
    @25
    @23
    @44
    @46
    vi
    @23
    c1
    @43
    fzfid
    #
    @23
    @45
    @44
    wcel
    #
    wa
    #
    @45
    @49
    @45
    cn
    wcel
    @23
    @45
    @43
    elfznn
    #
    adantl
    #
    nnrecred
    fsumrecl
    @41
    @23
    @42
    clog
    cfv
    #
    @3
    @47
    cle
    @5
    @53
    @3
    wceq
    wph
    @21
    @0
    logsqrt
    ad2antrl
    @23
    @42
    crp
    wcel
    #
    @53
    @47
    cle
    wbr
    @5
    @54
    wph
    @21
    @0
    rpsqrtcl
    ad2antrl
    #
    @42
    vi
    harmoniclbnd
    syl
    eqbrtrrd
    @23
    @15
    @18
    cn
    wcel
    #
    c1
    cc0
    cif
    #
    @18
    cdiv
    co
    #
    vk
    csu
    #
    @47
    @20
    cle
    @23
    vm
    @44
    vm
    cv
    #
    c2
    cexp
    co
    #
    cmpt
    #
    crn
    #
    @58
    vk
    csu
    #
    @44
    c1
    @45
    c2
    cexp
    co
    #
    csqrt
    cfv
    #
    cdiv
    co
    #
    vi
    csu
    #
    @59
    @47
    @23
    @64
    @63
    c1
    @18
    cdiv
    co
    #
    vk
    csu
    @68
    @23
    @63
    @58
    @69
    vk
    @23
    @16
    @63
    wcel
    #
    wa
    #
    @57
    c1
    @18
    cdiv
    @71
    @56
    c1
    cc0
    @23
    @70
    @56
    @70
    @16
    @61
    wceq
    #
    vm
    @44
    wrex
    @23
    @56
    vm
    @44
    @61
    @16
    @62
    @62
    eqid
    #
    @60
    c2
    cexp
    ovex
    #
    elrnmpti
    @23
    @72
    @56
    vm
    @44
    @23
    @60
    @44
    wcel
    #
    wa
    #
    @56
    @72
    @61
    csqrt
    cfv
    #
    cn
    wcel
    @76
    @77
    @60
    cn
    @76
    @60
    cr
    wcel
    cc0
    @60
    cle
    wbr
    wa
    #
    @77
    @60
    wceq
    @76
    @60
    @76
    @60
    @75
    @60
    cn
    wcel
    #
    @23
    @60
    @43
    elfznn
    #
    adantl
    #
    nnrpd
    rprege0d
    #
    @60
    sqrtsq
    syl
    @81
    eqeltrd
    @72
    @18
    @77
    cn
    @16
    @61
    csqrt
    fveq2
    eleq1d
    syl5ibrcom
    rexlimdva
    syl5bi
    imp
    iftrued
    oveq1d
    #
    sumeq2dv
    @23
    @63
    @69
    @44
    @67
    vk
    vi
    @62
    @65
    @16
    @65
    wceq
    @18
    @66
    c1
    cdiv
    @16
    @65
    csqrt
    fveq2
    oveq2d
    @48
    @23
    @44
    @15
    @62
    wf1
    #
    @44
    @63
    @62
    wf1o
    @23
    vm
    vi
    @44
    @15
    @61
    @65
    @23
    @75
    @61
    @15
    wcel
    #
    @76
    @85
    @61
    cn
    wcel
    #
    @61
    @0
    cle
    wbr
    #
    @76
    @60
    @81
    nnsqcld
    @76
    @61
    @42
    c2
    cexp
    co
    #
    @0
    cle
    @76
    @60
    @42
    cle
    wbr
    #
    @61
    @88
    cle
    wbr
    #
    @23
    @75
    @79
    @89
    @23
    @42
    cr
    wcel
    #
    @75
    @79
    @89
    wa
    wb
    @23
    @42
    @55
    rpred
    @60
    @42
    fznnfl
    syl
    simplbda
    @76
    @78
    @91
    cc0
    @42
    cle
    wbr
    wa
    @89
    @90
    wb
    @82
    @76
    @42
    @23
    @54
    @75
    @55
    adantr
    rprege0d
    @60
    @42
    le2sq
    syl2anc
    mpbid
    @76
    @0
    @76
    @0
    @23
    @0
    cr
    wcel
    #
    @75
    @23
    @0
    @30
    rpred
    #
    adantr
    #
    recnd
    sqsqrtd
    breqtrd
    @76
    @92
    @85
    @86
    @87
    wa
    wb
    @94
    @61
    @0
    fznnfl
    syl
    mpbir2and
    ex
    @75
    @49
    wa
    @61
    @65
    wceq
    @60
    @45
    wceq
    wb
    #
    wi
    @23
    @75
    @78
    @45
    cr
    wcel
    cc0
    @45
    cle
    wbr
    wa
    #
    @95
    @49
    @75
    @60
    @75
    @60
    @80
    nnrpd
    rprege0d
    @49
    @45
    @49
    @45
    @51
    nnrpd
    rprege0d
    @60
    @45
    sq11
    syl2an
    a1i
    dom2lem
    #
    @44
    @15
    @62
    f1f1orn
    syl
    @49
    @45
    @62
    cfv
    @65
    wceq
    @23
    vm
    @45
    @61
    @65
    @44
    @62
    @60
    @45
    c2
    cexp
    oveq1
    @73
    @74
    fvmpt3i
    adantl
    @71
    @58
    @69
    cc
    @83
    @23
    @70
    @32
    @58
    cc
    wcel
    @23
    @63
    @15
    @16
    @23
    @84
    @44
    @15
    @62
    wf
    @63
    @15
    wss
    @97
    @44
    @15
    @62
    f1f
    @44
    @15
    @62
    frn
    3syl
    #
    sselda
    @33
    @58
    @33
    @57
    cr
    wcel
    #
    @18
    crp
    wcel
    #
    @58
    cr
    wcel
    @56
    c1
    cc0
    cr
    1re
    0re
    keepel
    #
    @39
    @57
    @18
    rerpdivcl
    sylancr
    #
    recnd
    syldan
    #
    eqeltrrd
    fsumf1o
    eqtrd
    @23
    @63
    @15
    @58
    vk
    @98
    @103
    @23
    @16
    @15
    @63
    cdif
    wcel
    #
    wa
    #
    @58
    cc0
    @18
    cdiv
    co
    #
    cc0
    @105
    @57
    cc0
    @18
    cdiv
    @105
    @56
    c1
    cc0
    @104
    @23
    @32
    @70
    wn
    #
    wa
    @56
    wn
    #
    @16
    @15
    @63
    eldif
    @23
    @32
    @107
    @108
    @33
    @56
    @70
    @23
    @32
    @56
    @70
    @23
    @32
    @56
    wa
    #
    wa
    #
    @18
    c2
    cexp
    co
    #
    @16
    @63
    @110
    @16
    @110
    @16
    @32
    @35
    @23
    @56
    @36
    ad2antrl
    #
    nncnd
    sqsqrtd
    #
    @110
    @18
    @44
    wcel
    #
    @111
    cn
    wcel
    @111
    @63
    wcel
    @110
    @114
    @56
    @18
    @42
    cle
    wbr
    #
    @23
    @32
    @56
    simprr
    @110
    @16
    @0
    cle
    wbr
    #
    @115
    @23
    @32
    @116
    @56
    @23
    @32
    @35
    @116
    @23
    @92
    @32
    @35
    @116
    wa
    wb
    @93
    @16
    @0
    fznnfl
    syl
    simplbda
    adantrr
    @110
    @16
    cr
    wcel
    cc0
    @16
    cle
    wbr
    wa
    @92
    cc0
    @0
    cle
    wbr
    wa
    @116
    @115
    wb
    @110
    @16
    @110
    @16
    @112
    nnrpd
    rprege0d
    @110
    @0
    @23
    @5
    @109
    @30
    adantr
    rprege0d
    @16
    @0
    sqrtle
    syl2anc
    mpbid
    @110
    @91
    @114
    @56
    @115
    wa
    wb
    @110
    @42
    @23
    @54
    @109
    @55
    adantr
    rpred
    @18
    @42
    fznnfl
    syl
    mpbir2and
    @110
    @111
    @16
    cn
    @113
    @112
    eqeltrd
    vm
    @44
    @61
    @111
    @18
    @62
    cn
    @73
    @60
    @18
    c2
    cexp
    oveq1
    elrnmpt1s
    syl2anc
    eqeltrrd
    expr
    con3d
    impr
    sylan2b
    iffalsed
    oveq1d
    @105
    @18
    cc
    wcel
    @18
    cc0
    wne
    wa
    @106
    cc0
    wceq
    @105
    @18
    @104
    @23
    @32
    @100
    @16
    @15
    @63
    eldifi
    @39
    sylan2
    rpcnne0d
    @18
    div0
    syl
    eqtrd
    @31
    fsumss
    @23
    @44
    @67
    @46
    vi
    @50
    @66
    @45
    c1
    cdiv
    @50
    @96
    @66
    @45
    wceq
    @50
    @45
    @50
    @45
    @52
    nnrpd
    rprege0d
    @45
    sqrtsq
    syl
    oveq2d
    sumeq2dv
    3eqtr3d
    @23
    @15
    @58
    @19
    vk
    @31
    @102
    @40
    @33
    @57
    @17
    @18
    @99
    @33
    @101
    a1i
    @37
    @39
    @33
    vv
    @16
    cD
    c.1
    cF
    cG
    cL
    cN
    cX
    cZ
    vq
    vb
    rpvmasum.z
    rpvmasum.l
    wph
    cN
    cn
    wcel
    @22
    @32
    rpvmasum.a
    ad2antrr
    rpvmasum2.g
    rpvmasum2.d
    rpvmasum2.1
    dchrisum0f.f
    wph
    cX
    cD
    wcel
    @22
    @32
    dchrisum0f.x
    ad2antrr
    wph
    cZ
    cbs
    cfv
    cr
    cX
    wf
    @22
    @32
    dchrisum0flb.r
    ad2antrr
    @38
    dchrisum0flb
    lediv1dd
    fsumle
    eqbrtrrd
    letrd
    @23
    @20
    @41
    leabsd
    letrd
    eqbrtrd
    o1le
    o1mul2
    eqeltrrd
    mto
end
