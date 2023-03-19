include "ccnp.mm"
include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "cres.mm"
include "crest.mm"
include "ccn.mm"
include "cuni.mm"
include "cvmlift3lem3.mm"
include "ccom.mm"
include "cvmlift3lem5.mm"
include "eqeltrd.mm"
include "csconn.mm"
include "ctop.mm"
include "sconntop.mm"
include "syl.mm"
include "ccnv.mm"
include "cima.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wf.mm"
include "wceq.mm"
include "eqid.mm"
include "cnf.mm"
include "fdm.mm"
include "3syl.mm"
include "syl5sseq.mm"
include "sstrd.mm"
include "sseldd.mm"
include "ccvm.mm"
include "wa.mm"
include "ffvelrnd.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "fveq1d.mm"
include "eqtr3d.mm"
include "cvmsiota.mm"
include "syl13anc.mm"
include "wss.mm"
include "cv.mm"
include "wral.mm"
include "cc0.mm"
include "c1.mm"
include "cii.mm"
include "crio.mm"
include "w3a.mm"
include "wrex.mm"
include "cvmlift3lem4.mm"
include "mpbii.mm"
include "mpdan.mm"
include "adantr.mm"
include "weq.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "coeq2.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "riotabidv.mm"
include "anbi12d.mm"
include "cbvriotav.mm"
include "syl6eqr.mm"
include "3anbi123d.mm"
include "cbvrexv.mm"
include "sylib.mm"
include "cpconn.mm"
include "restuni.mm"
include "eleqtrd.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "pconncn.mm"
include "syl3anc.mm"
include "reeanv.mm"
include "ad3antrrr.mm"
include "cnlly.mm"
include "simpllr.mm"
include "simplrl.mm"
include "simprl.mm"
include "simplrr.mm"
include "simprr.mm"
include "cvmlift3lem6.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "mp2and.mm"
include "ralrimiva.mm"
include "wfun.mm"
include "wb.mm"
include "ffun.mm"
include "sseqtr4d.mm"
include "funimass4.mm"
include "mpbird.mm"
include "cvmlift2lem9a.mm"
include "cncnpi.mm"
include "cnt.mm"
include "ssntr.mm"
include "syl22anc.mm"
include "cnprest.mm"

theorem cvmlift3lem7
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cM: class M
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vw: setvar w
  let cI: class I
  let va: setvar a
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vh: setvar h
  let vn: setvar n
  let cN: class N
  let vm: setvar m
  let vt: setvar t
  let cQ: class Q
  let cR: class R
  let cZ: class Z
  assume cvmlift3.b: |- B = U. C
  assume cvmlift3.y: |- Y = U. K
  assume cvmlift3.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmlift3.k: |- ( ph -> K e. SConn )
  assume cvmlift3.l: |- ( ph -> K e. N-Locally PConn )
  assume cvmlift3.o: |- ( ph -> O e. Y )
  assume cvmlift3.g: |- ( ph -> G e. ( K Cn J ) )
  assume cvmlift3.p: |- ( ph -> P e. B )
  assume cvmlift3.e: |- ( ph -> ( F ` P ) = ( G ` O ) )
  assume cvmlift3.h: |- H = ( x e. Y |-> ( iota_ z e. B E. f e. ( II Cn K ) ( ( f ` 0 ) = O /\ ( f ` 1 ) = x /\ ( ( iota_ g e. ( II Cn C ) ( ( F o. g ) = ( G o. f ) /\ ( g ` 0 ) = P ) ) ` 1 ) = z ) ) )
  assume cvmlift3lem7.s: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. c e. s ( A. d e. ( s \ { c } ) ( c i^i d ) = (/) /\ ( F |` c ) e. ( ( C |`t c ) Homeo ( J |`t k ) ) ) ) } )
  assume cvmlift3lem7.1: |- ( ph -> ( G ` X ) e. A )
  assume cvmlift3lem7.2: |- ( ph -> T e. ( S ` A ) )
  assume cvmlift3lem7.3: |- ( ph -> M C_ ( `' G " A ) )
  assume cvmlift3lem7.w: |- W = ( iota_ b e. T ( H ` X ) e. b )
  assume cvmlift3lem7.7: |- ( ph -> ( K |`t M ) e. PConn )
  assume cvmlift3lem7.4: |- ( ph -> V e. K )
  assume cvmlift3lem7.5: |- ( ph -> V C_ M )
  assume cvmlift3lem7.6: |- ( ph -> X e. V )

  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b k
  disjoint b s
  disjoint b z
  disjoint A b
  disjoint c d
  disjoint c f
  disjoint c k
  disjoint c s
  disjoint c z
  disjoint A c
  disjoint d f
  disjoint d k
  disjoint d s
  disjoint d z
  disjoint A d
  disjoint f k
  disjoint f s
  disjoint f z
  disjoint A f
  disjoint k s
  disjoint k z
  disjoint A k
  disjoint s z
  disjoint A s
  disjoint A z
  disjoint f g
  disjoint g z
  disjoint b g
  disjoint b x
  disjoint J b
  disjoint c g
  disjoint c x
  disjoint J c
  disjoint d g
  disjoint d x
  disjoint J d
  disjoint f x
  disjoint J f
  disjoint g k
  disjoint g s
  disjoint g x
  disjoint J g
  disjoint k x
  disjoint J k
  disjoint s x
  disjoint J s
  disjoint J x
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F f
  disjoint F g
  disjoint F k
  disjoint F s
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint M f
  disjoint M g
  disjoint M x
  disjoint H b
  disjoint H c
  disjoint H d
  disjoint H f
  disjoint H g
  disjoint H x
  disjoint H z
  disjoint S b
  disjoint S f
  disjoint S x
  disjoint B b
  disjoint B d
  disjoint B f
  disjoint B g
  disjoint B x
  disjoint B z
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X f
  disjoint X g
  disjoint X x
  disjoint X z
  disjoint G b
  disjoint G c
  disjoint G d
  disjoint G f
  disjoint G g
  disjoint G k
  disjoint G x
  disjoint G z
  disjoint T b
  disjoint T c
  disjoint T d
  disjoint T s
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint C f
  disjoint C g
  disjoint C k
  disjoint C s
  disjoint C x
  disjoint C z
  disjoint f ph
  disjoint ph x
  disjoint K b
  disjoint K c
  disjoint K f
  disjoint K g
  disjoint K x
  disjoint K z
  disjoint P b
  disjoint P c
  disjoint P d
  disjoint P f
  disjoint P g
  disjoint P x
  disjoint P z
  disjoint O b
  disjoint O c
  disjoint O f
  disjoint O g
  disjoint O x
  disjoint O z
  disjoint Y f
  disjoint Y g
  disjoint Y x
  disjoint Y z
  disjoint W c
  disjoint W d
  disjoint W f
  disjoint W x
  disjoint b w
  disjoint c w
  disjoint d w
  disjoint f w
  disjoint k w
  disjoint s w
  disjoint w z
  disjoint A w
  disjoint I f
  disjoint g w
  disjoint I g
  disjoint I w
  disjoint I z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a g
  disjoint a k
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint J a
  disjoint b u
  disjoint b v
  disjoint b y
  disjoint c u
  disjoint c v
  disjoint c y
  disjoint d u
  disjoint d v
  disjoint d y
  disjoint f u
  disjoint f v
  disjoint f y
  disjoint g u
  disjoint g v
  disjoint g y
  disjoint k u
  disjoint k v
  disjoint k y
  disjoint s u
  disjoint s v
  disjoint s y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint J u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint J v
  disjoint w x
  disjoint w y
  disjoint J w
  disjoint x y
  disjoint J y
  disjoint a h
  disjoint a n
  disjoint a z
  disjoint F a
  disjoint b h
  disjoint b n
  disjoint c h
  disjoint c n
  disjoint d h
  disjoint d n
  disjoint f h
  disjoint f n
  disjoint g h
  disjoint g n
  disjoint h k
  disjoint h n
  disjoint h s
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint F h
  disjoint k n
  disjoint n s
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint u z
  disjoint F u
  disjoint v z
  disjoint F v
  disjoint F w
  disjoint y z
  disjoint F y
  disjoint M h
  disjoint M n
  disjoint M y
  disjoint N f
  disjoint N g
  disjoint N w
  disjoint a m
  disjoint a t
  disjoint H a
  disjoint b m
  disjoint b t
  disjoint c m
  disjoint c t
  disjoint d m
  disjoint d t
  disjoint f m
  disjoint f t
  disjoint g m
  disjoint g t
  disjoint h m
  disjoint h t
  disjoint H h
  disjoint m n
  disjoint m t
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint H m
  disjoint n t
  disjoint H n
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint H t
  disjoint H v
  disjoint H w
  disjoint H y
  disjoint Q f
  disjoint Q g
  disjoint Q w
  disjoint S a
  disjoint S m
  disjoint S t
  disjoint S v
  disjoint B a
  disjoint B h
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B y
  disjoint R g
  disjoint R w
  disjoint X a
  disjoint X h
  disjoint X n
  disjoint X w
  disjoint G a
  disjoint G h
  disjoint k m
  disjoint k t
  disjoint m u
  disjoint G m
  disjoint G n
  disjoint t u
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G y
  disjoint Z f
  disjoint Z g
  disjoint Z x
  disjoint Z z
  disjoint C a
  disjoint C h
  disjoint m s
  disjoint C m
  disjoint C n
  disjoint s t
  disjoint C t
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C y
  disjoint a ph
  disjoint h ph
  disjoint m ph
  disjoint n ph
  disjoint ph t
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint K a
  disjoint K h
  disjoint K m
  disjoint K n
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K y
  disjoint P a
  disjoint P h
  disjoint P n
  disjoint P u
  disjoint P v
  disjoint P w
  disjoint O a
  disjoint O h
  disjoint O n
  disjoint O u
  disjoint O v
  disjoint O w
  disjoint Y a
  disjoint Y h
  disjoint Y m
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y y
  disjoint W h
  disjoint W n
  disjoint W y
  assert |- ( ph -> H e. ( ( K CnP C ) ` X ) )

  proof
    wph
    cH
    cX
    cK
    cC
    ccnp
    co
    cfv
    wcel
    #
    cH
    cM
    cres
    #
    cX
    cK
    cM
    crest
    co
    #
    cC
    ccnp
    co
    cfv
    wcel
    #
    wph
    @1
    @2
    cC
    ccn
    co
    wcel
    cX
    @2
    cuni
    #
    wcel
    #
    @3
    wph
    cA
    cB
    cC
    cS
    cT
    vk
    cF
    cH
    cJ
    cK
    cM
    cW
    cX
    cY
    vs
    vc
    vd
    cvmlift3.b
    cvmlift3.y
    cvmlift3lem7.s
    cvmlift3.f
    wph
    vx
    vz
    cB
    cC
    cP
    vf
    vg
    cF
    cG
    cH
    cJ
    cK
    cO
    cY
    cvmlift3.b
    cvmlift3.y
    cvmlift3.f
    cvmlift3.k
    cvmlift3.l
    cvmlift3.o
    cvmlift3.g
    cvmlift3.p
    cvmlift3.e
    cvmlift3.h
    cvmlift3lem3
    #
    wph
    cF
    cH
    ccom
    #
    cG
    cK
    cJ
    ccn
    co
    #
    wph
    vx
    vz
    cB
    cC
    cP
    vf
    vg
    cF
    cG
    cH
    cJ
    cK
    cO
    cY
    cvmlift3.b
    cvmlift3.y
    cvmlift3.f
    cvmlift3.k
    cvmlift3.l
    cvmlift3.o
    cvmlift3.g
    cvmlift3.p
    cvmlift3.e
    cvmlift3.h
    cvmlift3lem5
    #
    cvmlift3.g
    eqeltrd
    wph
    cK
    csconn
    wcel
    #
    cK
    ctop
    wcel
    #
    cvmlift3.k
    cK
    sconntop
    syl
    #
    wph
    cM
    cY
    cX
    wph
    cM
    cG
    ccnv
    cA
    cima
    #
    cY
    cvmlift3lem7.3
    wph
    cG
    cdm
    #
    @13
    cY
    cG
    cA
    cnvimass
    wph
    cG
    @8
    wcel
    #
    cY
    cJ
    cuni
    #
    cG
    wf
    @14
    cY
    wceq
    cvmlift3.g
    cG
    cK
    cJ
    cY
    @16
    cvmlift3.y
    @16
    eqid
    cnf
    cY
    @16
    cG
    fdm
    3syl
    syl5sseq
    sstrd
    #
    wph
    cV
    cM
    cX
    cvmlift3lem7.5
    cvmlift3lem7.6
    sseldd
    #
    sseldd
    #
    cvmlift3lem7.2
    wph
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    cT
    cA
    cS
    cfv
    wcel
    #
    cX
    cH
    cfv
    #
    cB
    wcel
    @22
    cF
    cfv
    #
    cA
    wcel
    cW
    cT
    wcel
    @22
    cW
    wcel
    wa
    cvmlift3.f
    cvmlift3lem7.2
    wph
    cY
    cB
    cX
    cH
    @6
    @19
    ffvelrnd
    wph
    @23
    cX
    cG
    cfv
    #
    cA
    wph
    cX
    @7
    cfv
    #
    @23
    @24
    wph
    cY
    cB
    cH
    wf
    #
    cX
    cY
    wcel
    #
    @25
    @23
    wceq
    @6
    @19
    cY
    cB
    cX
    cF
    cH
    fvco3
    syl2anc
    wph
    cX
    @7
    cG
    @9
    fveq1d
    eqtr3d
    cvmlift3lem7.1
    eqeltrd
    vb
    vd
    vc
    @22
    cB
    cC
    cS
    cT
    cA
    vk
    cF
    cJ
    cW
    vs
    cvmlift3lem7.s
    cvmlift3.b
    cvmlift3lem7.w
    cvmsiota
    syl13anc
    @17
    wph
    cH
    cM
    cima
    cW
    wss
    #
    vy
    cv
    #
    cH
    cfv
    cW
    wcel
    #
    vy
    cM
    wral
    #
    wph
    @30
    vy
    cM
    wph
    @29
    cM
    wcel
    #
    wa
    #
    cc0
    vh
    cv
    #
    cfv
    #
    cO
    wceq
    #
    c1
    @34
    cfv
    #
    cX
    wceq
    #
    c1
    cF
    va
    cv
    #
    ccom
    #
    cG
    @34
    ccom
    #
    wceq
    #
    cc0
    @39
    cfv
    #
    cP
    wceq
    #
    wa
    #
    va
    cii
    cC
    ccn
    co
    #
    crio
    #
    cfv
    #
    @22
    wceq
    #
    w3a
    #
    vh
    cii
    cK
    ccn
    co
    #
    wrex
    #
    cc0
    vn
    cv
    #
    cfv
    cX
    wceq
    c1
    @53
    cfv
    @29
    wceq
    wa
    #
    vn
    cii
    @2
    ccn
    co
    #
    wrex
    #
    @30
    @33
    cc0
    vf
    cv
    #
    cfv
    #
    cO
    wceq
    #
    c1
    @57
    cfv
    #
    cX
    wceq
    #
    c1
    cF
    vg
    cv
    #
    ccom
    #
    cG
    @57
    ccom
    #
    wceq
    #
    cc0
    @62
    cfv
    #
    cP
    wceq
    #
    wa
    #
    vg
    @46
    crio
    #
    cfv
    #
    @22
    wceq
    #
    w3a
    #
    vf
    @51
    wrex
    #
    @52
    wph
    @73
    @32
    wph
    @27
    @73
    @19
    wph
    @27
    wa
    @22
    @22
    wceq
    @73
    @22
    eqid
    wph
    vx
    vz
    @22
    cB
    cC
    cP
    vf
    vg
    cF
    cG
    cH
    cJ
    cK
    cO
    cX
    cY
    cvmlift3.b
    cvmlift3.y
    cvmlift3.f
    cvmlift3.k
    cvmlift3.l
    cvmlift3.o
    cvmlift3.g
    cvmlift3.p
    cvmlift3.e
    cvmlift3.h
    cvmlift3lem4
    mpbii
    mpdan
    adantr
    @72
    @50
    vf
    vh
    @51
    vf
    vh
    weq
    #
    @59
    @36
    @61
    @38
    @71
    @49
    @74
    @58
    @35
    cO
    cc0
    @57
    @34
    fveq1
    eqeq1d
    @74
    @60
    @37
    cX
    c1
    @57
    @34
    fveq1
    eqeq1d
    @74
    @70
    @48
    @22
    @74
    c1
    @69
    @47
    @74
    @69
    @63
    @41
    wceq
    #
    @67
    wa
    #
    vg
    @46
    crio
    @47
    @74
    @68
    @76
    vg
    @46
    @74
    @65
    @75
    @67
    @74
    @64
    @41
    @63
    @57
    @34
    cG
    coeq2
    eqeq2d
    anbi1d
    riotabidv
    @45
    @76
    va
    vg
    @46
    va
    vg
    weq
    #
    @42
    @75
    @44
    @67
    @77
    @40
    @63
    @41
    @39
    @62
    cF
    coeq2
    #
    eqeq1d
    @77
    @43
    @66
    cP
    cc0
    @39
    @62
    fveq1
    #
    eqeq1d
    anbi12d
    cbvriotav
    #
    syl6eqr
    fveq1d
    eqeq1d
    3anbi123d
    cbvrexv
    sylib
    @33
    @2
    cpconn
    wcel
    #
    @5
    @29
    @4
    wcel
    #
    @56
    wph
    @81
    @32
    cvmlift3lem7.7
    adantr
    wph
    @5
    @32
    wph
    cX
    cM
    @4
    @18
    wph
    @11
    cM
    cY
    wss
    #
    cM
    @4
    wceq
    @12
    @17
    cM
    cK
    cY
    cvmlift3.y
    restuni
    syl2anc
    #
    eleqtrd
    #
    adantr
    wph
    @32
    @82
    wph
    cM
    @4
    @29
    @84
    eleq2d
    biimpa
    cX
    @29
    vn
    @2
    @4
    @4
    eqid
    #
    pconncn
    syl3anc
    @52
    @56
    wa
    @50
    @54
    wa
    #
    vn
    @55
    wrex
    vh
    @51
    wrex
    @33
    @30
    @50
    @54
    vh
    vn
    @51
    @55
    reeanv
    @33
    @87
    @30
    vh
    vn
    @51
    @55
    @33
    @34
    @51
    wcel
    #
    @53
    @55
    wcel
    #
    wa
    #
    wa
    #
    @87
    @30
    @91
    @87
    wa
    vx
    vz
    cA
    cB
    cC
    cP
    @34
    @47
    cS
    cT
    vf
    vg
    vk
    cF
    cG
    cH
    @40
    cG
    @53
    ccom
    #
    wceq
    #
    @43
    @22
    wceq
    #
    wa
    #
    va
    @46
    crio
    cJ
    cK
    cM
    @53
    cO
    cW
    cX
    cY
    @29
    vs
    vb
    vc
    vd
    cvmlift3.b
    cvmlift3.y
    wph
    @20
    @32
    @90
    @87
    cvmlift3.f
    ad3antrrr
    wph
    @10
    @32
    @90
    @87
    cvmlift3.k
    ad3antrrr
    wph
    cK
    cpconn
    cnlly
    wcel
    @32
    @90
    @87
    cvmlift3.l
    ad3antrrr
    wph
    cO
    cY
    wcel
    @32
    @90
    @87
    cvmlift3.o
    ad3antrrr
    wph
    @15
    @32
    @90
    @87
    cvmlift3.g
    ad3antrrr
    wph
    cP
    cB
    wcel
    @32
    @90
    @87
    cvmlift3.p
    ad3antrrr
    wph
    cP
    cF
    cfv
    cO
    cG
    cfv
    wceq
    @32
    @90
    @87
    cvmlift3.e
    ad3antrrr
    cvmlift3.h
    cvmlift3lem7.s
    wph
    @24
    cA
    wcel
    @32
    @90
    @87
    cvmlift3lem7.1
    ad3antrrr
    wph
    @21
    @32
    @90
    @87
    cvmlift3lem7.2
    ad3antrrr
    wph
    cM
    @13
    wss
    @32
    @90
    @87
    cvmlift3lem7.3
    ad3antrrr
    cvmlift3lem7.w
    wph
    cX
    cM
    wcel
    @32
    @90
    @87
    @18
    ad3antrrr
    wph
    @32
    @90
    @87
    simpllr
    @33
    @88
    @89
    @87
    simplrl
    @80
    @91
    @50
    @54
    simprl
    @33
    @88
    @89
    @87
    simplrr
    @91
    @50
    @54
    simprr
    @95
    @63
    @92
    wceq
    #
    @66
    @22
    wceq
    #
    wa
    va
    vg
    @46
    @77
    @93
    @96
    @94
    @97
    @77
    @40
    @63
    @92
    @78
    eqeq1d
    @77
    @43
    @66
    @22
    @79
    eqeq1d
    anbi12d
    cbvriotav
    cvmlift3lem6
    ex
    rexlimdvva
    syl5bir
    mp2and
    ralrimiva
    wph
    cH
    wfun
    #
    cM
    cH
    cdm
    #
    wss
    @28
    @31
    wb
    wph
    @26
    @98
    @6
    cY
    cB
    cH
    ffun
    syl
    wph
    cM
    cY
    @99
    @17
    wph
    @26
    @99
    cY
    wceq
    @6
    cY
    cB
    cH
    fdm
    syl
    sseqtr4d
    vy
    cM
    cW
    cH
    funimass4
    syl2anc
    mpbird
    cvmlift2lem9a
    @85
    cX
    @1
    @2
    cC
    @4
    @86
    cncnpi
    syl2anc
    wph
    @11
    @83
    cX
    cM
    cK
    cnt
    cfv
    cfv
    #
    wcel
    @26
    @0
    @3
    wb
    @12
    @17
    wph
    cV
    @100
    cX
    wph
    @11
    @83
    cV
    cK
    wcel
    cV
    cM
    wss
    cV
    @100
    wss
    @12
    @17
    cvmlift3lem7.4
    cvmlift3lem7.5
    cM
    cK
    cV
    cY
    cvmlift3.y
    ssntr
    syl22anc
    cvmlift3lem7.6
    sseldd
    @6
    cM
    cX
    cH
    cK
    cC
    cY
    cB
    cvmlift3.y
    cvmlift3.b
    cnprest
    syl22anc
    mpbird
end
