include "crp.mm"
include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cmin.mm"
include "cabs.mm"
include "cdiv.mm"
include "csu.mm"
include "cmu.mm"
include "cmul.mm"
include "cr.mm"
include "1red.mm"
include "dchrvmasumlem2.mm"
include "wcel.mm"
include "wa.mm"
include "fzfid.mm"
include "cc.mm"
include "wral.mm"
include "simpr.mm"
include "elfznn.mm"
include "nnrpd.mm"
include "rpdivcl.mm"
include "syl2an.mm"
include "ralrimiva.mm"
include "ad2antrr.mm"
include "wceq.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "subcld.mm"
include "abscld.mm"
include "cn.mm"
include "adantl.mm"
include "nndivred.mm"
include "fsumrecl.mm"
include "cz.mm"
include "elfzelz.mm"
include "dchrzrhcl.mm"
include "mucl.mm"
include "syl.mm"
include "zred.mm"
include "recnd.mm"
include "mulcld.mm"
include "fsumcl.mm"
include "cle.mm"
include "wbr.mm"
include "fsumabs.mm"
include "nnrecred.mm"
include "absge0d.mm"
include "absmuld.mm"
include "cbs.mm"
include "eqid.mm"
include "wf.mm"
include "wfo.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "znzrhfo.mm"
include "fof.mm"
include "ffvelrnd.mm"
include "dchrabs2.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "absdivd.mm"
include "cc0.mm"
include "rprege0d.mm"
include "absid.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "mule1.mm"
include "lediv1dd.mm"
include "eqbrtrd.mm"
include "lemul12ad.mm"
include "mulid2d.mm"
include "breqtrd.mm"
include "lemul1ad.mm"
include "divrec2d.mm"
include "3brtr4d.mm"
include "fsumle.mm"
include "letrd.mm"
include "leabsd.mm"
include "adantrr.mm"
include "o1le.mm"

theorem dchrvmasumlem3
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cR: class R
  let cT: class T
  let c.1: class .1.
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cK: class K
  let cL: class L
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vd: setvar d
  let vk: setvar k
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
  let ve: setvar e
  let vr: setvar r
  let cI: class I
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vq: setvar q
  let vv: setvar v
  let cA: class A
  let cE: class E
  let cP: class P
  let wps: wff ps
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
  assume dchrvmasum.f: |- ( ( ph /\ m e. RR+ ) -> F e. CC )
  assume dchrvmasum.g: |- ( m = ( x / d ) -> F = K )
  assume dchrvmasum.c: |- ( ph -> C e. ( 0 [,) +oo ) )
  assume dchrvmasum.t: |- ( ph -> T e. CC )
  assume dchrvmasum.1: |- ( ( ph /\ m e. ( 3 [,) +oo ) ) -> ( abs ` ( F - T ) ) <_ ( C x. ( ( log ` m ) / m ) ) )
  assume dchrvmasum.r: |- ( ph -> R e. RR )
  assume dchrvmasum.2: |- ( ph -> A. m e. ( 1 [,) 3 ) ( abs ` ( F - T ) ) <_ R )

  disjoint m x
  disjoint .1. m
  disjoint .1. x
  disjoint d m
  disjoint d x
  disjoint C d
  disjoint C m
  disjoint C x
  disjoint F d
  disjoint F x
  disjoint K m
  disjoint N m
  disjoint N x
  disjoint d ph
  disjoint m ph
  disjoint ph x
  disjoint T d
  disjoint T m
  disjoint T x
  disjoint R d
  disjoint R m
  disjoint R x
  disjoint Z m
  disjoint Z x
  disjoint D m
  disjoint D x
  disjoint L d
  disjoint L m
  disjoint L x
  disjoint X d
  disjoint X m
  disjoint X x
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
  disjoint .1. y
  disjoint .1. z
  disjoint d n
  disjoint d y
  disjoint C n
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
  disjoint T y
  disjoint R c
  disjoint R i
  disjoint R k
  disjoint R n
  disjoint R u
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
  disjoint Z y
  disjoint Z z
  disjoint D c
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D k
  disjoint D n
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
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( x e. RR+ |-> sum_ d e. ( 1 ... ( |_ ` x ) ) ( ( ( X ` ( L ` d ) ) x. ( ( mmu ` d ) / d ) ) x. ( K - T ) ) ) e. O(1) )

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
    cK
    cT
    cmin
    co
    #
    cabs
    cfv
    #
    vd
    cv
    #
    cdiv
    co
    #
    vd
    csu
    #
    @2
    @5
    cL
    cfv
    #
    cX
    cfv
    #
    @5
    cmu
    cfv
    #
    @5
    cdiv
    co
    #
    cmul
    co
    #
    @3
    cmul
    co
    #
    vd
    csu
    #
    c1
    cr
    wph
    1red
    wph
    vx
    cC
    cD
    cR
    cT
    c.1
    vm
    cF
    cG
    cK
    cL
    cN
    cX
    cZ
    vd
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    rpvmasum.g
    rpvmasum.d
    rpvmasum.1
    dchrisum.b
    dchrisum.n1
    dchrvmasum.f
    dchrvmasum.g
    dchrvmasum.c
    dchrvmasum.t
    dchrvmasum.1
    dchrvmasum.r
    dchrvmasum.2
    dchrvmasumlem2
    wph
    @0
    crp
    wcel
    #
    wa
    #
    @2
    @6
    vd
    @16
    c1
    @1
    fzfid
    #
    @16
    @5
    @2
    wcel
    #
    wa
    #
    @4
    @5
    @19
    @3
    @19
    cK
    cT
    @19
    @0
    @5
    cdiv
    co
    #
    crp
    wcel
    #
    cF
    cc
    wcel
    #
    vm
    crp
    wral
    #
    cK
    cc
    wcel
    #
    @16
    @15
    @5
    crp
    wcel
    @21
    @18
    wph
    @15
    simpr
    @18
    @5
    @5
    @1
    elfznn
    #
    nnrpd
    @0
    @5
    rpdivcl
    syl2an
    wph
    @23
    @15
    @18
    wph
    @22
    vm
    crp
    dchrvmasum.f
    ralrimiva
    ad2antrr
    @22
    @24
    vm
    @20
    crp
    vm
    cv
    @20
    wceq
    cF
    cK
    cc
    dchrvmasum.g
    eleq1d
    rspcv
    sylc
    wph
    cT
    cc
    wcel
    @15
    @18
    dchrvmasum.t
    ad2antrr
    subcld
    #
    abscld
    #
    @18
    @5
    cn
    wcel
    #
    @16
    @25
    adantl
    #
    nndivred
    #
    fsumrecl
    #
    @16
    @2
    @13
    vd
    @17
    @19
    @12
    @3
    @19
    @9
    @11
    @19
    @5
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
    @15
    @18
    dchrisum.b
    ad2antrr
    #
    @18
    @5
    cz
    wcel
    @16
    @5
    c1
    @1
    elfzelz
    adantl
    #
    dchrzrhcl
    #
    @19
    @11
    @19
    @10
    @5
    @19
    @10
    @19
    @28
    @10
    cz
    wcel
    @29
    @5
    mucl
    syl
    zred
    #
    @29
    nndivred
    recnd
    #
    mulcld
    #
    @26
    mulcld
    #
    fsumcl
    #
    wph
    @15
    @14
    cabs
    cfv
    #
    @7
    cabs
    cfv
    #
    cle
    wbr
    c1
    @0
    cle
    wbr
    @16
    @40
    @7
    @41
    @16
    @14
    @39
    abscld
    #
    @31
    @16
    @7
    @16
    @7
    @31
    recnd
    abscld
    @16
    @40
    @2
    @13
    cabs
    cfv
    #
    vd
    csu
    @7
    @42
    @16
    @2
    @43
    vd
    @17
    @19
    @13
    @38
    abscld
    #
    fsumrecl
    @31
    @16
    @2
    @13
    vd
    @17
    @38
    fsumabs
    @16
    @2
    @43
    @6
    vd
    @17
    @44
    @30
    @19
    @12
    cabs
    cfv
    #
    @4
    cmul
    co
    c1
    @5
    cdiv
    co
    #
    @4
    cmul
    co
    @43
    @6
    cle
    @19
    @45
    @46
    @4
    @19
    @12
    @37
    abscld
    @19
    @5
    @29
    nnrecred
    #
    @27
    @19
    @3
    @26
    absge0d
    @19
    @45
    @9
    cabs
    cfv
    #
    @11
    cabs
    cfv
    #
    cmul
    co
    #
    @46
    cle
    @19
    @9
    @11
    @34
    @36
    absmuld
    @19
    @50
    c1
    @46
    cmul
    co
    @46
    cle
    @19
    @48
    c1
    @49
    @46
    @19
    @9
    @34
    abscld
    @19
    1red
    #
    @19
    @11
    @36
    abscld
    @47
    @19
    @9
    @34
    absge0d
    @19
    @11
    @36
    absge0d
    @19
    @8
    cZ
    cbs
    cfv
    #
    cD
    cG
    cN
    cX
    cZ
    rpvmasum.g
    rpvmasum.d
    rpvmasum.z
    @52
    eqid
    #
    @32
    @19
    cz
    @52
    @5
    cL
    wph
    cz
    @52
    cL
    wf
    #
    @15
    @18
    wph
    cz
    @52
    cL
    wfo
    #
    @54
    wph
    cN
    cn0
    wcel
    @55
    wph
    cN
    rpvmasum.a
    nnnn0d
    @52
    cL
    cN
    cZ
    rpvmasum.z
    @53
    rpvmasum.l
    znzrhfo
    syl
    cz
    @52
    cL
    fof
    syl
    ad2antrr
    @33
    ffvelrnd
    dchrabs2
    @19
    @49
    @10
    cabs
    cfv
    #
    @5
    cdiv
    co
    #
    @46
    cle
    @19
    @49
    @56
    @5
    cabs
    cfv
    #
    cdiv
    co
    @57
    @19
    @10
    @5
    @19
    @10
    @35
    recnd
    #
    @19
    @5
    @29
    nncnd
    #
    @19
    @5
    @29
    nnne0d
    #
    absdivd
    @19
    @58
    @5
    @56
    cdiv
    @19
    @5
    cr
    wcel
    cc0
    @5
    cle
    wbr
    wa
    @58
    @5
    wceq
    @19
    @5
    @19
    @5
    @29
    nnrpd
    #
    rprege0d
    @5
    absid
    syl
    oveq2d
    eqtrd
    @19
    @56
    c1
    @5
    @19
    @10
    @59
    abscld
    @51
    @62
    @19
    @28
    @56
    c1
    cle
    wbr
    @29
    @5
    mule1
    syl
    lediv1dd
    eqbrtrd
    lemul12ad
    @19
    @46
    @19
    @46
    @47
    recnd
    mulid2d
    breqtrd
    eqbrtrd
    lemul1ad
    @19
    @12
    @3
    @37
    @26
    absmuld
    @19
    @4
    @5
    @19
    @4
    @27
    recnd
    @60
    @61
    divrec2d
    3brtr4d
    fsumle
    letrd
    @16
    @7
    @31
    leabsd
    letrd
    adantrr
    o1le
end
