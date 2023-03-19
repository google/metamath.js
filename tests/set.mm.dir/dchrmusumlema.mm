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
include "oveq2.mm"
include "wcel.mm"
include "1nn.mm"
include "a1i.mm"
include "crp.mm"
include "rpreccl.mm"
include "adantl.mm"
include "rpred.mm"
include "w3a.mm"
include "simp3r.mm"
include "wb.mm"
include "cr.mm"
include "clt.mm"
include "rpregt0.mm"
include "lerec.mm"
include "syl2an.mm"
include "3ad2ant2.mm"
include "mpbid.mm"
include "cc.mm"
include "crli.mm"
include "ax-1cn.mm"
include "divrcnv.mm"
include "mp1i.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "dchrisum.mm"
include "wceq.mm"
include "adantr.mm"
include "cz.mm"
include "nnz.mm"
include "dchrzrhcl.mm"
include "nncn.mm"
include "wne.mm"
include "nnne0.mm"
include "divrecd.mm"
include "mpteq2dva.mm"
include "id.mm"
include "eqtri.mm"
include "3eqtr4g.mm"
include "seqeq3d.mm"
include "breq1d.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "cbvralv.mm"
include "fveq1d.mm"
include "ad2antrr.mm"
include "elrege0.mm"
include "simplbi.mm"
include "recnd.mm"
include "ad2antlr.mm"
include "1re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "0red.mm"
include "1red.mm"
include "0lt1.mm"
include "simprbi.mm"
include "ltletrd.mm"
include "gt0ne0d.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "rexbidva.mm"
include "exbidv.mm"
include "mpbird.mm"

theorem dchrmusumlema
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
  let vm: setvar m
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
  assume dchrisumn0.f: |- F = ( a e. NN |-> ( ( X ` ( L ` a ) ) / a ) )

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
  assert |- ( ph -> E. t E. c e. ( 0 [,) +oo ) ( seq 1 ( + , F ) ~~> t /\ A. y e. ( 1 [,) +oo ) ( abs ` ( ( seq 1 ( + , F ) ` ( |_ ` y ) ) - t ) ) <_ ( c / y ) ) )

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
    @16
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
    @22
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
    @24
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
    @11
    wral
    #
    wa
    #
    vc
    @14
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
    cdiv
    co
    #
    @29
    cD
    c.1
    vn
    @21
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
    rpvmasum.g
    rpvmasum.d
    rpvmasum.1
    dchrisum.b
    dchrisum.n1
    @35
    @24
    c1
    cdiv
    oveq2
    c1
    cn
    wcel
    wph
    1nn
    a1i
    wph
    @35
    crp
    wcel
    #
    wa
    @36
    @37
    @36
    crp
    wcel
    wph
    @35
    rpreccl
    adantl
    rpred
    wph
    @37
    @24
    crp
    wcel
    #
    wa
    #
    c1
    @35
    cle
    wbr
    #
    @35
    @24
    cle
    wbr
    #
    wa
    #
    w3a
    @41
    @29
    @36
    cle
    wbr
    #
    wph
    @39
    @40
    @41
    simp3r
    @39
    wph
    @41
    @43
    wb
    #
    @42
    @37
    @35
    cr
    wcel
    cc0
    @35
    clt
    wbr
    wa
    @24
    cr
    wcel
    #
    cc0
    @24
    clt
    wbr
    wa
    @44
    @38
    @35
    rpregt0
    @24
    rpregt0
    @35
    @24
    lerec
    syl2an
    3ad2ant2
    mpbid
    c1
    cc
    wcel
    vn
    crp
    @36
    cmpt
    cc0
    crli
    wbr
    wph
    ax-1cn
    c1
    vn
    divrcnv
    mp1i
    va
    vn
    cn
    @20
    @35
    cL
    cfv
    #
    cX
    cfv
    #
    @36
    cmul
    co
    #
    va
    vn
    weq
    #
    @18
    @47
    @19
    @36
    cmul
    @49
    @17
    @46
    cX
    @16
    @35
    cL
    fveq2
    fveq2d
    #
    @16
    @35
    c1
    cdiv
    oveq2
    oveq12d
    cbvmptv
    #
    dchrisum
    wph
    @15
    @34
    vt
    wph
    @13
    @33
    vc
    @14
    wph
    @8
    @14
    wcel
    #
    wa
    #
    @2
    @23
    @12
    @32
    @53
    @0
    @22
    @1
    cli
    @53
    cF
    @21
    caddc
    c1
    wph
    cF
    @21
    wceq
    @52
    wph
    vn
    cn
    @47
    @35
    cdiv
    co
    #
    cmpt
    #
    vn
    cn
    @48
    cmpt
    cF
    @21
    wph
    vn
    cn
    @54
    @48
    wph
    @35
    cn
    wcel
    #
    wa
    #
    @47
    @35
    @57
    @35
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
    @56
    dchrisum.b
    adantr
    @56
    @35
    cz
    wcel
    wph
    @35
    nnz
    adantl
    dchrzrhcl
    @56
    @35
    cc
    wcel
    wph
    @35
    nncn
    adantl
    @56
    @35
    cc0
    wne
    wph
    @35
    nnne0
    adantl
    divrecd
    mpteq2dva
    cF
    va
    cn
    @18
    @16
    cdiv
    co
    #
    cmpt
    @55
    dchrisumn0.f
    va
    vn
    cn
    @58
    @54
    @49
    @18
    @47
    @16
    @35
    cdiv
    @50
    @49
    id
    oveq12d
    cbvmptv
    eqtri
    @51
    3eqtr4g
    #
    adantr
    seqeq3d
    breq1d
    @12
    @25
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
    @24
    cdiv
    co
    #
    cle
    wbr
    #
    vx
    @11
    wral
    @53
    @32
    @10
    @64
    vy
    vx
    @11
    vy
    vx
    weq
    #
    @7
    @62
    @9
    @63
    cle
    @65
    @6
    @61
    cabs
    @65
    @5
    @60
    @1
    cmin
    @65
    @4
    @25
    @0
    @3
    @24
    cfl
    fveq2
    fveq2d
    oveq1d
    fveq2d
    @3
    @24
    @8
    cdiv
    oveq2
    breq12d
    cbvralv
    @53
    @64
    @31
    vx
    @11
    @53
    @24
    @11
    wcel
    #
    wa
    #
    @62
    @28
    @63
    @30
    cle
    wph
    @62
    @28
    wceq
    @52
    @66
    wph
    @61
    @27
    cabs
    wph
    @60
    @26
    @1
    cmin
    wph
    @25
    @0
    @22
    wph
    cF
    @21
    caddc
    c1
    @59
    seqeq3d
    fveq1d
    oveq1d
    fveq2d
    ad2antrr
    @67
    @8
    @24
    @52
    @8
    cc
    wcel
    wph
    @66
    @52
    @8
    @52
    @8
    cr
    wcel
    cc0
    @8
    cle
    wbr
    @8
    elrege0
    simplbi
    recnd
    ad2antlr
    @67
    @24
    @66
    @45
    @53
    @66
    @45
    c1
    @24
    cle
    wbr
    #
    c1
    cr
    wcel
    @66
    @45
    @68
    wa
    wb
    1re
    c1
    @24
    elicopnf
    ax-mp
    #
    simplbi
    adantl
    #
    recnd
    @67
    @24
    @67
    cc0
    c1
    @24
    @67
    0red
    @67
    1red
    @70
    cc0
    c1
    clt
    wbr
    @67
    0lt1
    a1i
    @66
    @68
    @53
    @66
    @45
    @68
    @69
    simprbi
    adantl
    ltletrd
    gt0ne0d
    divrecd
    breq12d
    ralbidva
    syl5bb
    anbi12d
    rexbidva
    exbidv
    mpbird
end
