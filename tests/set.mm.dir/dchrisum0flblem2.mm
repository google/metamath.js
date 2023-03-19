include "csqrt.mm"
include "cfv.mm"
include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cpc.mm"
include "co.mm"
include "cexp.mm"
include "cdiv.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "breq1.mm"
include "wa.mm"
include "1t1e1.mm"
include "c2.mm"
include "cprime.mm"
include "cq.mm"
include "wne.mm"
include "cz.mm"
include "wceq.mm"
include "adantr.mm"
include "nnq.mm"
include "adantl.mm"
include "nnne0.mm"
include "2z.mm"
include "a1i.mm"
include "pcexp.mm"
include "syl121anc.mm"
include "cc.mm"
include "cuz.mm"
include "eluz2nn.mm"
include "syl.mm"
include "nncnd.mm"
include "sqsqrtd.mm"
include "oveq2d.mm"
include "2cnd.mm"
include "simpr.mm"
include "pccld.mm"
include "nn0cnd.mm"
include "mulcomd.mm"
include "3eqtr3rd.mm"
include "prmnn.mm"
include "cn0.mm"
include "2nn0.mm"
include "expmuld.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "cr.mm"
include "nnexpcld.mm"
include "nnrpd.mm"
include "rprege0d.mm"
include "sqrtsq.mm"
include "eqtrd.mm"
include "eqeltrd.mm"
include "iftrued.mm"
include "dchrisum0flblem1.mm"
include "eqbrtrrd.mm"
include "clt.mm"
include "cdvds.mm"
include "pcdvds.mm"
include "syl2anc.mm"
include "wb.mm"
include "nndivdvds.mm"
include "mpbid.mm"
include "nnzd.mm"
include "crp.mm"
include "sqrtdiv.mm"
include "nnz.mm"
include "znq.mm"
include "zsqrtelqelz.mm"
include "sqrtgt0d.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "cfzo.mm"
include "cv.mm"
include "wral.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "nnred.mm"
include "pcelnn.mm"
include "mpbird.mm"
include "prmuz2.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "3syl.mm"
include "expgt1.mm"
include "syl3anc.mm"
include "1red.mm"
include "0lt1.mm"
include "nngt0d.mm"
include "ltdiv2.mm"
include "syl222anc.mm"
include "div1d.mm"
include "breqtrd.mm"
include "elfzo2.mm"
include "syl3anbrc.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "ifbid.mm"
include "breq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "wi.mm"
include "1re.mm"
include "0le1.mm"
include "pm3.2i.mm"
include "dchrisum0ff.mm"
include "ffvelrnd.mm"
include "lemul12a.mm"
include "syl22anc.mm"
include "mp2and.mm"
include "syl5eqbrr.mm"
include "wn.mm"
include "0red.mm"
include "0re.mm"
include "keepel.mm"
include "breq2.mm"
include "0le0.mm"
include "keephyp.mm"
include "letrd.mm"
include "mulge0d.mm"
include "ifbothda.mm"
include "nnne0d.mm"
include "divcan2d.mm"
include "cgcd.mm"
include "pcndvds2.mm"
include "coprm.mm"
include "prmz.mm"
include "rpexp1i.mm"
include "mpd.mm"
include "dchrisum0fmul.mm"
include "breqtrrd.mm"

theorem dchrisum0flblem2
  let wph: wff ph
  let vy: setvar y
  let vv: setvar v
  let cA: class A
  let cD: class D
  let cP: class P
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
  assume dchrisum0flb.1: |- ( ph -> A e. ( ZZ>= ` 2 ) )
  assume dchrisum0flb.2: |- ( ph -> P e. Prime )
  assume dchrisum0flb.3: |- ( ph -> P || A )
  assume dchrisum0flb.4: |- ( ph -> A. y e. ( 1 ..^ A ) if ( ( sqrt ` y ) e. NN , 1 , 0 ) <_ ( F ` y ) )

  disjoint .1. y
  disjoint F y
  disjoint b q
  disjoint b v
  disjoint b y
  disjoint A b
  disjoint q v
  disjoint q y
  disjoint A q
  disjoint v y
  disjoint A v
  disjoint A y
  disjoint N q
  disjoint N y
  disjoint P b
  disjoint P q
  disjoint P v
  disjoint P y
  disjoint Z y
  disjoint D y
  disjoint L b
  disjoint L v
  disjoint L y
  disjoint X b
  disjoint X v
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
  disjoint q z
  disjoint t v
  disjoint A t
  disjoint v x
  disjoint v z
  disjoint A x
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
  disjoint N z
  disjoint b n
  disjoint P i
  disjoint P k
  disjoint P m
  disjoint n v
  disjoint P n
  disjoint P x
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
  disjoint X z
  assert |- ( ph -> if ( ( sqrt ` A ) e. NN , 1 , 0 ) <_ ( F ` A ) )

  proof
    wph
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
    cP
    cP
    cA
    cpc
    co
    #
    cexp
    co
    #
    cF
    cfv
    #
    cA
    @4
    cdiv
    co
    #
    cF
    cfv
    #
    cmul
    co
    #
    cA
    cF
    cfv
    #
    cle
    @1
    c1
    @8
    cle
    wbr
    cc0
    @8
    cle
    wbr
    #
    @2
    @8
    cle
    wbr
    wph
    c1
    cc0
    c1
    @2
    @8
    cle
    breq1
    cc0
    @2
    @8
    cle
    breq1
    wph
    @1
    wa
    #
    c1
    c1
    c1
    cmul
    co
    #
    @8
    cle
    1t1e1
    @11
    c1
    @5
    cle
    wbr
    #
    c1
    @7
    cle
    wbr
    #
    @12
    @8
    cle
    wbr
    #
    @11
    @4
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
    c1
    @5
    cle
    @11
    @17
    c1
    cc0
    @11
    @16
    cP
    cP
    @0
    cpc
    co
    #
    cexp
    co
    #
    cn
    @11
    @16
    @20
    c2
    cexp
    co
    #
    csqrt
    cfv
    #
    @20
    @11
    @4
    @21
    csqrt
    @11
    cP
    @19
    c2
    cmul
    co
    #
    cexp
    co
    @4
    @21
    @11
    @23
    @3
    cP
    cexp
    @11
    cP
    @0
    c2
    cexp
    co
    #
    cpc
    co
    #
    c2
    @19
    cmul
    co
    #
    @3
    @23
    @11
    cP
    cprime
    wcel
    #
    @0
    cq
    wcel
    #
    @0
    cc0
    wne
    #
    c2
    cz
    wcel
    #
    @25
    @26
    wceq
    wph
    @27
    @1
    dchrisum0flb.2
    adantr
    #
    @1
    @28
    wph
    @0
    nnq
    adantl
    @1
    @29
    wph
    @0
    nnne0
    adantl
    @30
    @11
    2z
    a1i
    @0
    cP
    c2
    pcexp
    syl121anc
    @11
    @24
    cA
    cP
    cpc
    @11
    cA
    wph
    cA
    cc
    wcel
    @1
    wph
    cA
    wph
    cA
    c2
    cuz
    cfv
    #
    wcel
    cA
    cn
    wcel
    #
    dchrisum0flb.1
    cA
    eluz2nn
    syl
    #
    nncnd
    #
    adantr
    sqsqrtd
    oveq2d
    @11
    c2
    @19
    @11
    2cnd
    @11
    @19
    @11
    cP
    @0
    @31
    wph
    @1
    simpr
    pccld
    #
    nn0cnd
    mulcomd
    3eqtr3rd
    oveq2d
    @11
    cP
    @19
    c2
    @11
    cP
    @11
    @27
    cP
    cn
    wcel
    #
    @31
    cP
    prmnn
    #
    syl
    #
    nncnd
    c2
    cn0
    wcel
    @11
    2nn0
    a1i
    @36
    expmuld
    eqtr3d
    fveq2d
    @11
    @20
    cr
    wcel
    cc0
    @20
    cle
    wbr
    wa
    @22
    @20
    wceq
    @11
    @20
    @11
    @20
    @11
    cP
    @19
    @39
    @36
    nnexpcld
    #
    nnrpd
    rprege0d
    @20
    sqrtsq
    syl
    eqtrd
    @40
    eqeltrd
    #
    iftrued
    wph
    @18
    @5
    cle
    wbr
    @1
    wph
    vv
    @3
    cD
    cP
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
    dchrisum0flb.2
    wph
    cP
    cA
    dchrisum0flb.2
    @34
    pccld
    #
    dchrisum0flblem1
    #
    adantr
    eqbrtrrd
    @11
    @6
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
    c1
    @7
    cle
    @11
    @45
    c1
    cc0
    @11
    @44
    cz
    wcel
    #
    cc0
    @44
    clt
    wbr
    @45
    @11
    @6
    cz
    wcel
    #
    @44
    cq
    wcel
    @47
    wph
    @48
    @1
    wph
    @6
    wph
    @4
    cA
    cdvds
    wbr
    #
    @6
    cn
    wcel
    #
    wph
    @27
    @33
    @49
    dchrisum0flb.2
    @34
    cP
    cA
    pcdvds
    syl2anc
    wph
    @33
    @4
    cn
    wcel
    #
    @49
    @50
    wb
    @34
    wph
    cP
    @3
    wph
    @27
    @37
    dchrisum0flb.2
    @38
    syl
    #
    @42
    nnexpcld
    #
    cA
    @4
    nndivdvds
    syl2anc
    mpbid
    #
    nnzd
    #
    adantr
    @11
    @44
    @0
    @16
    cdiv
    co
    #
    cq
    @11
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    wa
    @4
    crp
    wcel
    @44
    @56
    wceq
    @11
    cA
    @11
    cA
    wph
    @33
    @1
    @34
    adantr
    nnrpd
    rprege0d
    @11
    @4
    wph
    @51
    @1
    @53
    adantr
    nnrpd
    cA
    @4
    sqrtdiv
    syl2anc
    @11
    @0
    cz
    wcel
    #
    @17
    @56
    cq
    wcel
    @1
    @58
    wph
    @0
    nnz
    adantl
    @41
    @0
    @16
    znq
    syl2anc
    eqeltrd
    @6
    zsqrtelqelz
    syl2anc
    @11
    @6
    @11
    @6
    wph
    @50
    @1
    @54
    adantr
    nnrpd
    sqrtgt0d
    @44
    elnnz
    sylanbrc
    iftrued
    wph
    @46
    @7
    cle
    wbr
    #
    @1
    wph
    @6
    c1
    cA
    cfzo
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
    @62
    cF
    cfv
    #
    cle
    wbr
    #
    vy
    @60
    wral
    @59
    wph
    @6
    c1
    cuz
    cfv
    #
    wcel
    cA
    cz
    wcel
    @6
    cA
    clt
    wbr
    @61
    wph
    @6
    cn
    @68
    @54
    nnuz
    syl6eleq
    wph
    cA
    @34
    nnzd
    wph
    @6
    cA
    c1
    cdiv
    co
    #
    cA
    clt
    wph
    c1
    @4
    clt
    wbr
    #
    @6
    @69
    clt
    wbr
    #
    wph
    cP
    cr
    wcel
    @3
    cn
    wcel
    #
    c1
    cP
    clt
    wbr
    #
    @70
    wph
    cP
    @52
    nnred
    wph
    @72
    cP
    cA
    cdvds
    wbr
    #
    dchrisum0flb.3
    wph
    @27
    @33
    @72
    @74
    wb
    dchrisum0flb.2
    @34
    cP
    cA
    pcelnn
    syl2anc
    mpbird
    wph
    @27
    cP
    @32
    wcel
    #
    @73
    dchrisum0flb.2
    cP
    prmuz2
    @75
    @37
    @73
    cP
    eluz2b2
    simprbi
    3syl
    cP
    @3
    expgt1
    syl3anc
    wph
    c1
    cr
    wcel
    #
    cc0
    c1
    clt
    wbr
    #
    @4
    cr
    wcel
    cc0
    @4
    clt
    wbr
    @57
    cc0
    cA
    clt
    wbr
    @70
    @71
    wb
    wph
    1red
    @77
    wph
    0lt1
    a1i
    wph
    @4
    @53
    nnred
    wph
    @4
    @53
    nngt0d
    wph
    cA
    @34
    nnred
    wph
    cA
    @34
    nngt0d
    c1
    @4
    cA
    ltdiv2
    syl222anc
    mpbid
    wph
    cA
    @35
    div1d
    breqtrd
    @6
    c1
    cA
    elfzo2
    syl3anbrc
    dchrisum0flb.4
    @67
    @59
    vy
    @6
    @60
    @62
    @6
    wceq
    #
    @65
    @46
    @66
    @7
    cle
    @78
    @64
    @45
    c1
    cc0
    @78
    @63
    @44
    cn
    @62
    @6
    csqrt
    fveq2
    eleq1d
    ifbid
    @62
    @6
    cF
    fveq2
    breq12d
    rspcv
    sylc
    #
    adantr
    eqbrtrrd
    @11
    @76
    cc0
    c1
    cle
    wbr
    #
    wa
    #
    @5
    cr
    wcel
    #
    @81
    @7
    cr
    wcel
    #
    @13
    @14
    wa
    @15
    wi
    @81
    @11
    @76
    @80
    1re
    0le1
    pm3.2i
    a1i
    #
    wph
    @82
    @1
    wph
    cn
    cr
    @4
    cF
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
    #
    @53
    ffvelrnd
    #
    adantr
    @84
    wph
    @83
    @1
    wph
    cn
    cr
    @6
    cF
    @85
    @54
    ffvelrnd
    #
    adantr
    c1
    @5
    c1
    @7
    lemul12a
    syl22anc
    mp2and
    syl5eqbrr
    wph
    @10
    @1
    wn
    wph
    @5
    @7
    @86
    @87
    wph
    cc0
    @18
    @5
    wph
    0red
    #
    @18
    cr
    wcel
    wph
    @17
    c1
    cc0
    cr
    1re
    0re
    keepel
    a1i
    @86
    cc0
    @18
    cle
    wbr
    #
    wph
    @17
    @80
    cc0
    cc0
    cle
    wbr
    #
    @89
    c1
    cc0
    c1
    @18
    cc0
    cle
    breq2
    cc0
    @18
    cc0
    cle
    breq2
    0le1
    0le0
    keephyp
    a1i
    @43
    letrd
    wph
    cc0
    @46
    @7
    @88
    @46
    cr
    wcel
    wph
    @45
    c1
    cc0
    cr
    1re
    0re
    keepel
    a1i
    @87
    cc0
    @46
    cle
    wbr
    #
    wph
    @45
    @80
    @90
    @91
    c1
    cc0
    c1
    @46
    cc0
    cle
    breq2
    cc0
    @46
    cc0
    cle
    breq2
    0le1
    0le0
    keephyp
    a1i
    @79
    letrd
    mulge0d
    adantr
    ifbothda
    wph
    @4
    @6
    cmul
    co
    #
    cF
    cfv
    @9
    @8
    wph
    @92
    cA
    cF
    wph
    cA
    @4
    @35
    wph
    @4
    @53
    nncnd
    wph
    @4
    @53
    nnne0d
    divcan2d
    fveq2d
    wph
    vv
    @4
    @6
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
    @53
    @54
    wph
    cP
    @6
    cgcd
    co
    c1
    wceq
    #
    @4
    @6
    cgcd
    co
    c1
    wceq
    #
    wph
    cP
    @6
    cdvds
    wbr
    wn
    #
    @93
    wph
    @27
    @33
    @95
    dchrisum0flb.2
    @34
    cP
    cA
    pcndvds2
    syl2anc
    wph
    @27
    @48
    @95
    @93
    wb
    dchrisum0flb.2
    @55
    cP
    @6
    coprm
    syl2anc
    mpbid
    wph
    cP
    cz
    wcel
    #
    @48
    @3
    cn0
    wcel
    @93
    @94
    wi
    wph
    @27
    @96
    dchrisum0flb.2
    cP
    prmz
    syl
    @55
    @42
    cP
    @6
    @3
    rpexp1i
    syl3anc
    mpd
    dchrisum0fmul
    eqtr3d
    breqtrrd
end
