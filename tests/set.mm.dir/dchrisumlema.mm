include "crp.mm"
include "wcel.mm"
include "csb.mm"
include "cr.mm"
include "wi.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "ralrimiva.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "cv.mm"
include "wceq.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "syl5com.mm"
include "wa.mm"
include "cmpt.mm"
include "cfl.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cuz.mm"
include "csn.mm"
include "cxp.mm"
include "eqid.mm"
include "wb.mm"
include "nnred.mm"
include "elicopnf.mm"
include "syl.mm"
include "simprbda.mm"
include "flcld.mm"
include "peano2zd.mm"
include "cli.mm"
include "cn.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cdm.mm"
include "nnrp.mm"
include "ssriv.mm"
include "dmmptd.mm"
include "syl5sseqr.mm"
include "rlimclim1.mm"
include "adantr.mm"
include "cc.mm"
include "cz.mm"
include "0red.mm"
include "clt.mm"
include "nngt0d.mm"
include "simplbda.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "sylc.mm"
include "recnd.mm"
include "ssid.mm"
include "fvex.mm"
include "climconst2.mm"
include "syl2anc.mm"
include "cn0.mm"
include "rpge0d.mm"
include "flge0nn0.mm"
include "nn0p1nn.mm"
include "eluznn.mm"
include "sylan.mm"
include "nnrpd.mm"
include "ad2antrr.mm"
include "weq.mm"
include "fvmpts.mm"
include "eqeltrd.mm"
include "fvconst2g.mm"
include "3expia.mm"
include "ralrimivva.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfbr.mm"
include "nfim.mm"
include "nfral.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "reflcl.mm"
include "peano2re.mm"
include "3syl.mm"
include "fllep1.mm"
include "eluzle.mm"
include "adantl.mm"
include "letrd.mm"
include "jca.mm"
include "anbi2d.mm"
include "cvv.mm"
include "eqvisset.mm"
include "equtr2.mm"
include "equcoms.mm"
include "csbied.mm"
include "eqcomd.mm"
include "breq1d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "3brtr4d.mm"
include "climle.mm"
include "ex.mm"

theorem dchrisumlema
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let c.1: class .1.
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vm: setvar m
  let vk: setvar k
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
  let cR: class R
  let cS: class S
  let cU: class U
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

  disjoint n x
  disjoint .1. n
  disjoint .1. x
  disjoint F n
  disjoint F x
  disjoint I n
  disjoint I x
  disjoint A x
  disjoint N n
  disjoint N x
  disjoint n ph
  disjoint ph x
  disjoint B n
  disjoint Z n
  disjoint Z x
  disjoint D n
  disjoint D x
  disjoint L n
  disjoint L x
  disjoint M n
  disjoint M x
  disjoint X n
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
  disjoint n u
  disjoint n w
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
  disjoint F u
  disjoint F y
  disjoint F z
  disjoint I i
  disjoint I k
  disjoint I u
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
  disjoint k ph
  disjoint m ph
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
  disjoint L u
  disjoint L v
  disjoint L y
  disjoint L z
  disjoint M c
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint M m
  disjoint M r
  disjoint M u
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
  disjoint X u
  disjoint X v
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( ( I e. RR+ -> [_ I / n ]_ A e. RR ) /\ ( I e. ( M [,) +oo ) -> 0 <_ [_ I / n ]_ A ) ) )

  proof
    wph
    cI
    crp
    wcel
    #
    vn
    cI
    cA
    csb
    #
    cr
    wcel
    #
    wi
    cI
    cM
    cpnf
    cico
    co
    wcel
    #
    cc0
    @1
    cle
    wbr
    #
    wi
    wph
    cA
    cr
    wcel
    #
    vn
    crp
    wral
    #
    @0
    @2
    wph
    @5
    vn
    crp
    dchrisum.4
    ralrimiva
    #
    @5
    @2
    vn
    cI
    crp
    vn
    @1
    cr
    vn
    cI
    cA
    nfcsb1v
    #
    nfel1
    vn
    cv
    #
    cI
    wceq
    #
    cA
    @1
    cr
    vn
    cI
    cA
    csbeq1a
    #
    eleq1d
    rspc
    #
    syl5com
    wph
    @3
    @4
    wph
    @3
    wa
    #
    cc0
    @1
    vi
    vn
    crp
    cA
    cmpt
    #
    cI
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    @1
    csn
    cxp
    #
    @16
    @17
    @17
    eqid
    @13
    @15
    @13
    cI
    wph
    @3
    cI
    cr
    wcel
    #
    cM
    cI
    cle
    wbr
    #
    wph
    cM
    cr
    wcel
    #
    @3
    @19
    @20
    wa
    wb
    wph
    cM
    dchrisum.3
    nnred
    #
    cM
    cI
    elicopnf
    syl
    #
    simprbda
    #
    flcld
    peano2zd
    #
    wph
    @14
    cc0
    cli
    wbr
    @3
    wph
    cc0
    @14
    c1
    cn
    nnuz
    wph
    1zzd
    dchrisum.6
    wph
    crp
    cn
    @14
    cdm
    vi
    cn
    crp
    vi
    cv
    #
    nnrp
    ssriv
    wph
    vn
    @14
    crp
    cA
    cr
    @14
    eqid
    #
    dchrisum.4
    dmmptd
    syl5sseqr
    rlimclim1
    adantr
    @13
    @1
    cc
    wcel
    @16
    cz
    wcel
    @18
    @1
    cli
    wbr
    @13
    @1
    @13
    @0
    @6
    @2
    @13
    cI
    @24
    @13
    cc0
    cM
    cI
    @13
    0red
    wph
    @21
    @3
    @22
    adantr
    @24
    wph
    cc0
    cM
    clt
    wbr
    @3
    wph
    cM
    dchrisum.3
    nngt0d
    adantr
    wph
    @3
    @19
    @20
    @23
    simplbda
    #
    ltletrd
    elrpd
    #
    wph
    @6
    @3
    @7
    adantr
    @12
    sylc
    #
    recnd
    @25
    @1
    @16
    @17
    @17
    ssid
    @16
    cuz
    fvex
    climconst2
    syl2anc
    @13
    @26
    @17
    wcel
    #
    wa
    #
    @26
    @14
    cfv
    #
    vn
    @26
    cA
    csb
    #
    cr
    @32
    @26
    crp
    wcel
    #
    @34
    cr
    wcel
    #
    @33
    @34
    wceq
    @32
    @26
    @13
    @16
    cn
    wcel
    #
    @31
    @26
    cn
    wcel
    @13
    @15
    cn0
    wcel
    #
    @37
    @13
    @19
    cc0
    cI
    cle
    wbr
    @38
    @24
    @13
    cI
    @29
    rpge0d
    cI
    flge0nn0
    syl2anc
    @15
    nn0p1nn
    syl
    @26
    @16
    eluznn
    sylan
    #
    nnrpd
    #
    @32
    @35
    @6
    @36
    @40
    wph
    @6
    @3
    @31
    @7
    ad2antrr
    @5
    @36
    vn
    @26
    crp
    vn
    @34
    cr
    vn
    @26
    cA
    nfcsb1v
    nfel1
    vn
    vi
    weq
    #
    cA
    @34
    cr
    vn
    @26
    cA
    csbeq1a
    eleq1d
    rspc
    sylc
    #
    vn
    @26
    cA
    crp
    @14
    cr
    @27
    fvmpts
    syl2anc
    #
    @42
    eqeltrd
    @32
    @26
    @18
    cfv
    #
    @1
    cr
    @13
    @2
    @31
    @44
    @1
    wceq
    @30
    @17
    @1
    @26
    cr
    fvconst2g
    sylan
    #
    @13
    @2
    @31
    @30
    adantr
    eqeltrd
    @32
    @34
    @1
    @33
    @44
    cle
    @32
    @35
    @20
    cI
    vx
    cv
    #
    cle
    wbr
    #
    wa
    #
    cB
    @1
    cle
    wbr
    #
    wi
    #
    vx
    crp
    wral
    #
    @20
    cI
    @26
    cle
    wbr
    #
    wa
    #
    @34
    @1
    cle
    wbr
    #
    @40
    @32
    @0
    cM
    @9
    cle
    wbr
    #
    @9
    @46
    cle
    wbr
    #
    wa
    #
    cB
    cA
    cle
    wbr
    #
    wi
    #
    vx
    crp
    wral
    #
    vn
    crp
    wral
    #
    @51
    @13
    @0
    @31
    @29
    adantr
    wph
    @61
    @3
    @31
    wph
    @59
    vn
    vx
    crp
    crp
    wph
    @9
    crp
    wcel
    @46
    crp
    wcel
    wa
    @57
    @58
    dchrisum.5
    3expia
    ralrimivva
    ad2antrr
    @60
    @51
    vn
    cI
    crp
    @50
    vn
    vx
    crp
    vn
    crp
    nfcv
    @48
    @49
    vn
    @48
    vn
    nfv
    vn
    cB
    @1
    cle
    vn
    cB
    nfcv
    vn
    cle
    nfcv
    @8
    nfbr
    nfim
    nfral
    @10
    @59
    @50
    vx
    crp
    @10
    @57
    @48
    @58
    @49
    @10
    @55
    @20
    @56
    @47
    @9
    cI
    cM
    cle
    breq2
    @9
    cI
    @46
    cle
    breq1
    anbi12d
    @10
    cA
    @1
    cB
    cle
    @11
    breq2d
    imbi12d
    ralbidv
    rspc
    sylc
    @32
    @20
    @52
    @13
    @20
    @31
    @28
    adantr
    @32
    cI
    @16
    @26
    @13
    @19
    @31
    @24
    adantr
    #
    @32
    @19
    @15
    cr
    wcel
    @16
    cr
    wcel
    @62
    cI
    reflcl
    @15
    peano2re
    3syl
    @32
    @26
    @39
    nnred
    @13
    cI
    @16
    cle
    wbr
    #
    @31
    @13
    @19
    @63
    @24
    cI
    fllep1
    syl
    adantr
    @31
    @16
    @26
    cle
    wbr
    @13
    @16
    @26
    eluzle
    adantl
    letrd
    jca
    @50
    @53
    @54
    wi
    vx
    @26
    crp
    vx
    vi
    weq
    #
    @48
    @53
    @49
    @54
    @64
    @47
    @52
    @20
    @46
    @26
    cI
    cle
    breq2
    anbi2d
    @64
    cB
    @34
    @1
    cle
    @64
    @34
    cB
    @64
    vn
    @26
    cA
    cB
    cvv
    vx
    @26
    eqvisset
    @64
    @41
    wa
    vx
    vn
    weq
    cA
    cB
    wceq
    #
    vx
    vn
    vi
    equtr2
    @65
    vn
    vx
    dchrisum.2
    equcoms
    syl
    csbied
    eqcomd
    breq1d
    imbi12d
    rspcv
    syl3c
    @43
    @45
    3brtr4d
    climle
    ex
    jca
end
