include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "csqrt.mm"
include "cfv.mm"
include "cn.mm"
include "cc0.mm"
include "cif.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cuz.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eluzfz2.mm"
include "syl.mm"
include "wi.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "raleqdv.mm"
include "imbi2d.mm"
include "c2.mm"
include "cexp.mm"
include "cprime.mm"
include "2prm.mm"
include "a1i.mm"
include "cn0.mm"
include "0nn0.mm"
include "dchrisum0flblem1.mm"
include "elfz1eq.mm"
include "2nn0.mm"
include "numexp0.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "eleq1d.mm"
include "ifbid.mm"
include "breq12d.mm"
include "biimprcd.mm"
include "ralrimiv.mm"
include "wa.mm"
include "csn.mm"
include "cdvds.mm"
include "wrex.mm"
include "simpr.mm"
include "adantrr.mm"
include "eluzp1p1.mm"
include "df-2.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "exprmfct.mm"
include "ad2antrr.mm"
include "cbs.mm"
include "cr.mm"
include "wf.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "cfzo.mm"
include "simplrr.mm"
include "cz.mm"
include "simplrl.mm"
include "nnzd.mm"
include "fzval3.mm"
include "mpbid.mm"
include "dchrisum0flblem2.mm"
include "rexlimddv.mm"
include "ovex.mm"
include "fveq2.mm"
include "ralsn.mm"
include "sylibr.mm"
include "expr.mm"
include "ancld.mm"
include "cun.mm"
include "fzsuc.mm"
include "ralunb.mm"
include "syl6bb.mm"
include "sylibrd.mm"
include "expcom.mm"
include "a2d.mm"
include "nnind.mm"
include "mpcom.mm"
include "rspcv.mm"
include "sylc.mm"

theorem dchrisum0flb
  let wph: wff ph
  let vv: setvar v
  let cA: class A
  let cD: class D
  let c.1: class .1.
  let cF: class F
  let cG: class G
  let cL: class L
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vq: setvar q
  let vb: setvar b
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
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
  assume dchrisum0flb.a: |- ( ph -> A e. NN )

  disjoint b q
  disjoint b v
  disjoint A b
  disjoint q v
  disjoint A q
  disjoint A v
  disjoint N q
  disjoint L b
  disjoint L v
  disjoint X b
  disjoint X v
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
  disjoint b t
  disjoint b x
  disjoint b y
  disjoint b z
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
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint t v
  disjoint A t
  disjoint v x
  disjoint v y
  disjoint v z
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
  disjoint N m
  disjoint n q
  disjoint N n
  disjoint N p
  disjoint q r
  disjoint q u
  disjoint N r
  disjoint N t
  disjoint N u
  disjoint N x
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
  disjoint Z m
  disjoint Z n
  disjoint Z p
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint D c
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D k
  disjoint D m
  disjoint D n
  disjoint D t
  disjoint D x
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
  disjoint L k
  disjoint L m
  disjoint L n
  disjoint L p
  disjoint L r
  disjoint L t
  disjoint u v
  disjoint L u
  disjoint L x
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
  disjoint X k
  disjoint X m
  disjoint X n
  disjoint X r
  disjoint X t
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> if ( ( sqrt ` A ) e. NN , 1 , 0 ) <_ ( F ` A ) )

  proof
    wph
    cA
    c1
    cA
    cfz
    co
    #
    wcel
    #
    vy
    cv
    #
    csqrt
    cfv
    #
    cn
    wcel
    #
    c1
    cc0
    cif
    #
    @2
    cF
    cfv
    #
    cle
    wbr
    #
    vy
    @0
    wral
    #
    cA
    csqrt
    cfv
    #
    cn
    wcel
    #
    c1
    cc0
    cif
    #
    cA
    cF
    cfv
    #
    cle
    wbr
    #
    wph
    cA
    c1
    cuz
    cfv
    #
    wcel
    @1
    wph
    cA
    cn
    @14
    dchrisum0flb.a
    nnuz
    syl6eleq
    c1
    cA
    eluzfz2
    syl
    cA
    cn
    wcel
    wph
    @8
    dchrisum0flb.a
    wph
    @7
    vy
    c1
    vk
    cv
    #
    cfz
    co
    #
    wral
    #
    wi
    wph
    @7
    vy
    c1
    c1
    cfz
    co
    #
    wral
    #
    wi
    wph
    @7
    vy
    c1
    vi
    cv
    #
    cfz
    co
    #
    wral
    #
    wi
    wph
    @7
    vy
    c1
    @20
    c1
    caddc
    co
    #
    cfz
    co
    #
    wral
    #
    wi
    wph
    @8
    wi
    vk
    vi
    cA
    @15
    c1
    wceq
    #
    @17
    @19
    wph
    @26
    @7
    vy
    @16
    @18
    @15
    c1
    c1
    cfz
    oveq2
    raleqdv
    imbi2d
    @15
    @20
    wceq
    #
    @17
    @22
    wph
    @27
    @7
    vy
    @16
    @21
    @15
    @20
    c1
    cfz
    oveq2
    raleqdv
    imbi2d
    @15
    @23
    wceq
    #
    @17
    @25
    wph
    @28
    @7
    vy
    @16
    @24
    @15
    @23
    c1
    cfz
    oveq2
    raleqdv
    imbi2d
    @15
    cA
    wceq
    #
    @17
    @8
    wph
    @29
    @7
    vy
    @16
    @0
    @15
    cA
    c1
    cfz
    oveq2
    raleqdv
    imbi2d
    wph
    c2
    cc0
    cexp
    co
    #
    csqrt
    cfv
    #
    cn
    wcel
    #
    c1
    cc0
    cif
    #
    @30
    cF
    cfv
    #
    cle
    wbr
    #
    @19
    wph
    vv
    cc0
    cD
    c2
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
    c2
    cprime
    wcel
    wph
    2prm
    a1i
    cc0
    cn0
    wcel
    wph
    0nn0
    a1i
    dchrisum0flblem1
    @35
    @7
    vy
    @18
    @2
    @18
    wcel
    #
    @7
    @35
    @36
    @5
    @33
    @6
    @34
    cle
    @36
    @4
    @32
    c1
    cc0
    @36
    @3
    @31
    cn
    @36
    @2
    @30
    csqrt
    @36
    @2
    c1
    @30
    @2
    c1
    elfz1eq
    c2
    2nn0
    numexp0
    syl6eqr
    #
    fveq2d
    eleq1d
    ifbid
    @36
    @2
    @30
    cF
    @37
    fveq2d
    breq12d
    biimprcd
    ralrimiv
    syl
    @20
    cn
    wcel
    #
    wph
    @22
    @25
    wph
    @38
    @22
    @25
    wi
    wph
    @38
    wa
    #
    @22
    @22
    @7
    vy
    @23
    csn
    #
    wral
    #
    wa
    #
    @25
    @39
    @22
    @41
    wph
    @38
    @22
    @41
    wph
    @38
    @22
    wa
    #
    wa
    #
    @23
    csqrt
    cfv
    #
    cn
    wcel
    #
    c1
    cc0
    cif
    #
    @23
    cF
    cfv
    #
    cle
    wbr
    #
    @41
    @44
    vp
    cv
    #
    @23
    cdvds
    wbr
    #
    @49
    vp
    cprime
    @44
    @23
    c2
    cuz
    cfv
    #
    wcel
    #
    @51
    vp
    cprime
    wrex
    @44
    @23
    c1
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    @52
    @44
    @20
    @14
    wcel
    #
    @23
    @55
    wcel
    wph
    @38
    @56
    @22
    @39
    @20
    cn
    @14
    wph
    @38
    simpr
    nnuz
    syl6eleq
    #
    adantrr
    c1
    @20
    eluzp1p1
    syl
    c2
    @54
    cuz
    df-2
    fveq2i
    syl6eleqr
    #
    @23
    vp
    exprmfct
    syl
    @44
    @50
    cprime
    wcel
    #
    @51
    wa
    #
    wa
    #
    vy
    vv
    @23
    cD
    @50
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
    @43
    @60
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
    @43
    @60
    dchrisum0f.x
    ad2antrr
    wph
    cZ
    cbs
    cfv
    cr
    cX
    wf
    @43
    @60
    dchrisum0flb.r
    ad2antrr
    @44
    @53
    @60
    @58
    adantr
    @44
    @59
    @51
    simprl
    @44
    @59
    @51
    simprr
    @61
    @22
    @7
    vy
    c1
    @23
    cfzo
    co
    #
    wral
    wph
    @38
    @22
    @60
    simplrr
    @61
    @7
    vy
    @21
    @62
    @61
    @20
    cz
    wcel
    @21
    @62
    wceq
    @61
    @20
    wph
    @38
    @22
    @60
    simplrl
    nnzd
    c1
    @20
    fzval3
    syl
    raleqdv
    mpbid
    dchrisum0flblem2
    rexlimddv
    @7
    @49
    vy
    @23
    @20
    c1
    caddc
    ovex
    @2
    @23
    wceq
    #
    @5
    @47
    @6
    @48
    cle
    @63
    @4
    @46
    c1
    cc0
    @63
    @3
    @45
    cn
    @2
    @23
    csqrt
    fveq2
    eleq1d
    ifbid
    @2
    @23
    cF
    fveq2
    breq12d
    ralsn
    sylibr
    expr
    ancld
    @39
    @25
    @7
    vy
    @21
    @40
    cun
    #
    wral
    @42
    @39
    @7
    vy
    @24
    @64
    @39
    @56
    @24
    @64
    wceq
    @57
    c1
    @20
    fzsuc
    syl
    raleqdv
    @7
    vy
    @21
    @40
    ralunb
    syl6bb
    sylibrd
    expcom
    a2d
    nnind
    mpcom
    @7
    @13
    vy
    cA
    @0
    @2
    cA
    wceq
    #
    @5
    @11
    @6
    @12
    cle
    @65
    @4
    @10
    c1
    cc0
    @65
    @3
    @9
    cn
    @2
    cA
    csqrt
    fveq2
    eleq1d
    ifbid
    @2
    cA
    cF
    fveq2
    breq12d
    rspcv
    sylc
end
