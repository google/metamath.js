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
include "clog.mm"
include "cdiv.mm"
include "cmul.mm"
include "cle.mm"
include "c3.mm"
include "cpnf.mm"
include "cico.mm"
include "wral.mm"
include "wa.mm"
include "cc0.mm"
include "wrex.mm"
include "wex.mm"
include "weq.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "cn.mm"
include "wcel.mm"
include "3nn.mm"
include "a1i.mm"
include "crp.mm"
include "cr.mm"
include "relogcl.mm"
include "rerpdivcl.mm"
include "mpancom.mm"
include "adantl.mm"
include "w3a.mm"
include "simp3r.mm"
include "ceu.mm"
include "wb.mm"
include "simp2l.mm"
include "rpred.mm"
include "ere.mm"
include "3re.mm"
include "c2.mm"
include "clt.mm"
include "egt2lt3.mm"
include "simpri.mm"
include "ltleii.mm"
include "simp3l.mm"
include "letrd.mm"
include "simp2r.mm"
include "logdivle.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "cmpt.mm"
include "ccxp.mm"
include "crli.mm"
include "rpcn.mm"
include "cxp1d.mm"
include "oveq2d.mm"
include "mpteq2ia.mm"
include "1rp.mm"
include "cxploglim.mm"
include "mp1i.mm"
include "syl5eqbrr.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "dchrisum.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "cbvralv.mm"
include "anbi2i.mm"
include "rexbii.mm"
include "exbii.mm"
include "sylib.mm"

theorem dchrvmasumlema
  let wph: wff ph
  let vy: setvar y
  let vt: setvar t
  let cD: class D
  let c.1: class .1.
  let cF: class F
  let cG: class G
  let cL: class L
  let cN: class N
  let cX: class X
  let cZ: class Z
  let va: setvar a
  let vc: setvar c
  let vk: setvar k
  let vm: setvar m
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
  assume dchrvmasumlema.f: |- F = ( a e. NN |-> ( ( X ` ( L ` a ) ) x. ( ( log ` a ) / a ) ) )

  disjoint c t
  disjoint c y
  disjoint .1. c
  disjoint t y
  disjoint .1. t
  disjoint .1. y
  disjoint F c
  disjoint F t
  disjoint F y
  disjoint a c
  disjoint a t
  disjoint a y
  disjoint N c
  disjoint N t
  disjoint N y
  disjoint c ph
  disjoint ph t
  disjoint Z y
  disjoint D c
  disjoint D t
  disjoint D y
  disjoint L a
  disjoint L c
  disjoint L t
  disjoint L y
  disjoint X a
  disjoint X c
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
  disjoint a m
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
  disjoint N m
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
  disjoint m ph
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
  disjoint W c
  disjoint W f
  disjoint W t
  disjoint W x
  disjoint W z
  disjoint Z f
  disjoint Z k
  disjoint Z m
  disjoint Z n
  disjoint Z p
  disjoint Z x
  disjoint Z z
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D k
  disjoint D m
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
  disjoint L m
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
  disjoint X m
  disjoint X n
  disjoint X r
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X z
  assert |- ( ph -> E. t E. c e. ( 0 [,) +oo ) ( seq 1 ( + , F ) ~~> t /\ A. y e. ( 3 [,) +oo ) ( abs ` ( ( seq 1 ( + , F ) ` ( |_ ` y ) ) - t ) ) <_ ( c x. ( ( log ` y ) / y ) ) ) )

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
    vx
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
    clog
    cfv
    #
    @3
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
    c3
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
    @2
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
    @8
    @18
    clog
    cfv
    #
    @18
    cdiv
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    vy
    @13
    wral
    #
    wa
    #
    vc
    @16
    wrex
    #
    vt
    wex
    wph
    vx
    vt
    vn
    cv
    #
    clog
    cfv
    #
    @30
    cdiv
    co
    #
    @10
    cD
    c.1
    vn
    cF
    cG
    cL
    c3
    cN
    cX
    cZ
    vc
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    rpvmasum.g
    rpvmasum.d
    rpvmasum.1
    dchrisum.b
    dchrisum.n1
    vn
    vx
    weq
    #
    @31
    @9
    @30
    @3
    cdiv
    @30
    @3
    clog
    fveq2
    @33
    id
    oveq12d
    c3
    cn
    wcel
    wph
    3nn
    a1i
    @30
    crp
    wcel
    #
    @32
    cr
    wcel
    #
    wph
    @31
    cr
    wcel
    @34
    @35
    @30
    relogcl
    @31
    @30
    rerpdivcl
    mpancom
    adantl
    wph
    @34
    @3
    crp
    wcel
    #
    wa
    #
    c3
    @30
    cle
    wbr
    #
    @30
    @3
    cle
    wbr
    #
    wa
    #
    w3a
    #
    @39
    @10
    @32
    cle
    wbr
    #
    wph
    @37
    @38
    @39
    simp3r
    #
    @41
    @30
    cr
    wcel
    ceu
    @30
    cle
    wbr
    @3
    cr
    wcel
    ceu
    @3
    cle
    wbr
    @39
    @42
    wb
    @41
    @30
    wph
    @34
    @36
    @40
    simp2l
    rpred
    #
    @41
    ceu
    c3
    @30
    ceu
    cr
    wcel
    @41
    ere
    a1i
    #
    c3
    cr
    wcel
    @41
    3re
    a1i
    @44
    ceu
    c3
    cle
    wbr
    @41
    ceu
    c3
    ere
    3re
    c2
    ceu
    clt
    wbr
    ceu
    c3
    clt
    wbr
    egt2lt3
    simpri
    ltleii
    a1i
    wph
    @37
    @38
    @39
    simp3l
    letrd
    #
    @41
    @3
    wph
    @34
    @36
    @40
    simp2r
    rpred
    #
    @41
    ceu
    @30
    @3
    @45
    @44
    @47
    @46
    @43
    letrd
    @30
    @3
    logdivle
    syl22anc
    mpbid
    wph
    vn
    crp
    @32
    cmpt
    vn
    crp
    @31
    @30
    c1
    ccxp
    co
    #
    cdiv
    co
    #
    cmpt
    #
    cc0
    crli
    vn
    crp
    @49
    @32
    @34
    @48
    @30
    @31
    cdiv
    @34
    @30
    @30
    rpcn
    cxp1d
    oveq2d
    mpteq2ia
    c1
    crp
    wcel
    @50
    cc0
    crli
    wbr
    wph
    1rp
    c1
    vn
    cxploglim
    mp1i
    syl5eqbrr
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
    @51
    clog
    cfv
    #
    @51
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    vn
    cn
    @30
    cL
    cfv
    #
    cX
    cfv
    #
    @32
    cmul
    co
    #
    cmpt
    dchrvmasumlema.f
    va
    vn
    cn
    @56
    @59
    va
    vn
    weq
    #
    @53
    @58
    @55
    @32
    cmul
    @60
    @52
    @57
    cX
    @51
    @30
    cL
    fveq2
    fveq2d
    @60
    @54
    @31
    @51
    @30
    cdiv
    @51
    @30
    clog
    fveq2
    @60
    id
    oveq12d
    oveq12d
    cbvmptv
    eqtri
    dchrisum
    @17
    @29
    vt
    @15
    @28
    vc
    @16
    @14
    @27
    @2
    @12
    @26
    vx
    vy
    @13
    vx
    vy
    weq
    #
    @7
    @22
    @11
    @25
    cle
    @61
    @6
    @21
    cabs
    @61
    @5
    @20
    @1
    cmin
    @61
    @4
    @19
    @0
    @3
    @18
    cfl
    fveq2
    fveq2d
    oveq1d
    fveq2d
    @61
    @10
    @24
    @8
    cmul
    @61
    @9
    @23
    @3
    @18
    cdiv
    @3
    @18
    clog
    fveq2
    @61
    id
    oveq12d
    oveq2d
    breq12d
    cbvralv
    anbi2i
    rexbii
    exbii
    sylib
end
