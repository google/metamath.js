include "cv.mm"
include "ccom.mm"
include "wceq.mm"
include "cfv.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "wrex.mm"
include "wrmo.mm"
include "wreu.mm"
include "cuni.mm"
include "ccnv.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cres.mm"
include "crest.mm"
include "chmeo.mm"
include "wcel.mm"
include "cpw.mm"
include "crab.mm"
include "cmpt.mm"
include "cc0.mm"
include "c1.mm"
include "cii.mm"
include "crio.mm"
include "w3a.mm"
include "weq.mm"
include "eqeq2.mm"
include "3anbi3d.mm"
include "rexbidv.mm"
include "cbvriotav.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "coeq2.mm"
include "anbi12d.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "riotabidv.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "3anbi123d.mm"
include "cbvrexv.mm"
include "3anbi2d.mm"
include "syl5bb.mm"
include "cbvmptv.mm"
include "eqid.mm"
include "cvmscbv.mm"
include "cvmlift3lem9.mm"
include "csconn.mm"
include "cpconn.mm"
include "cconn.mm"
include "sconnpconn.mm"
include "pconnconn.mm"
include "3syl.mm"
include "cnlly.mm"
include "wss.mm"
include "ssriv.mm"
include "nllyss.mm"
include "ax-mp.mm"
include "sseldi.mm"
include "cvmliftmo.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem cvmlift3
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cP: class P
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cO: class O
  let cY: class Y
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vs: setvar s
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let vg: setvar g
  let cI: class I
  let va: setvar a
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vh: setvar h
  let vn: setvar n
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vt: setvar t
  let cH: class H
  let cQ: class Q
  let cS: class S
  let cR: class R
  let cX: class X
  let cT: class T
  let cZ: class Z
  let cW: class W
  assume cvmlift3.b: |- B = U. C
  assume cvmlift3.y: |- Y = U. K
  assume cvmlift3.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmlift3.k: |- ( ph -> K e. SConn )
  assume cvmlift3.l: |- ( ph -> K e. N-Locally PConn )
  assume cvmlift3.o: |- ( ph -> O e. Y )
  assume cvmlift3.g: |- ( ph -> G e. ( K Cn J ) )
  assume cvmlift3.p: |- ( ph -> P e. B )
  assume cvmlift3.e: |- ( ph -> ( F ` P ) = ( G ` O ) )

  disjoint J f
  disjoint F f
  disjoint B f
  disjoint G f
  disjoint C f
  disjoint f ph
  disjoint K f
  disjoint P f
  disjoint O f
  disjoint Y f
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b k
  disjoint b s
  disjoint b w
  disjoint b z
  disjoint A b
  disjoint c d
  disjoint c f
  disjoint c k
  disjoint c s
  disjoint c w
  disjoint c z
  disjoint A c
  disjoint d f
  disjoint d k
  disjoint d s
  disjoint d w
  disjoint d z
  disjoint A d
  disjoint f k
  disjoint f s
  disjoint f w
  disjoint f z
  disjoint A f
  disjoint k s
  disjoint k w
  disjoint k z
  disjoint A k
  disjoint s w
  disjoint s z
  disjoint A s
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint f g
  disjoint I f
  disjoint g w
  disjoint g z
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
  disjoint b g
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint J b
  disjoint c g
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint c y
  disjoint J c
  disjoint d g
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint J d
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint g k
  disjoint g s
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint J g
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint J k
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint J s
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
  disjoint J x
  disjoint J y
  disjoint a h
  disjoint a n
  disjoint a z
  disjoint F a
  disjoint b h
  disjoint b n
  disjoint F b
  disjoint c h
  disjoint c n
  disjoint F c
  disjoint d h
  disjoint d n
  disjoint F d
  disjoint f h
  disjoint f n
  disjoint g h
  disjoint g n
  disjoint F g
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
  disjoint F k
  disjoint n s
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint F s
  disjoint u z
  disjoint F u
  disjoint v z
  disjoint F v
  disjoint F w
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint M f
  disjoint M g
  disjoint M h
  disjoint M n
  disjoint M x
  disjoint M y
  disjoint N f
  disjoint N g
  disjoint N w
  disjoint a m
  disjoint a t
  disjoint H a
  disjoint b m
  disjoint b t
  disjoint H b
  disjoint c m
  disjoint c t
  disjoint H c
  disjoint d m
  disjoint d t
  disjoint H d
  disjoint f m
  disjoint f t
  disjoint H f
  disjoint g m
  disjoint g t
  disjoint H g
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
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint Q f
  disjoint Q g
  disjoint Q w
  disjoint S a
  disjoint S b
  disjoint S f
  disjoint S m
  disjoint S t
  disjoint S v
  disjoint S x
  disjoint B a
  disjoint B b
  disjoint B d
  disjoint B g
  disjoint B h
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint R g
  disjoint R w
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X f
  disjoint X g
  disjoint X h
  disjoint X n
  disjoint X w
  disjoint X x
  disjoint X z
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G d
  disjoint G g
  disjoint G h
  disjoint k m
  disjoint k t
  disjoint G k
  disjoint m u
  disjoint G m
  disjoint G n
  disjoint t u
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint T b
  disjoint T c
  disjoint T d
  disjoint T s
  disjoint Z f
  disjoint Z g
  disjoint Z x
  disjoint Z z
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint C g
  disjoint C h
  disjoint C k
  disjoint m s
  disjoint C m
  disjoint C n
  disjoint s t
  disjoint C s
  disjoint C t
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint a ph
  disjoint h ph
  disjoint m ph
  disjoint n ph
  disjoint ph t
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint K g
  disjoint K h
  disjoint K m
  disjoint K n
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P d
  disjoint P g
  disjoint P h
  disjoint P n
  disjoint P u
  disjoint P v
  disjoint P w
  disjoint P x
  disjoint P z
  disjoint O a
  disjoint O b
  disjoint O c
  disjoint O g
  disjoint O h
  disjoint O n
  disjoint O u
  disjoint O v
  disjoint O w
  disjoint O x
  disjoint O z
  disjoint Y a
  disjoint Y g
  disjoint Y h
  disjoint Y m
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint W c
  disjoint W d
  disjoint W f
  disjoint W h
  disjoint W n
  disjoint W x
  disjoint W y
  assert |- ( ph -> E! f e. ( K Cn C ) ( ( F o. f ) = G /\ ( f ` O ) = P ) )

  proof
    wph
    cF
    vf
    cv
    #
    ccom
    cG
    wceq
    cO
    @0
    cfv
    cP
    wceq
    wa
    #
    vf
    cK
    cC
    ccn
    co
    #
    wrex
    @1
    vf
    @2
    wrmo
    @1
    vf
    @2
    wreu
    wph
    vx
    vz
    cB
    cC
    cP
    vk
    cJ
    vs
    cv
    #
    cuni
    cF
    ccnv
    vk
    cv
    #
    cima
    wceq
    vc
    cv
    #
    vd
    cv
    #
    cin
    c0
    wceq
    vd
    @3
    @5
    csn
    cdif
    wral
    cF
    @5
    cres
    cC
    @5
    crest
    co
    cJ
    @4
    crest
    co
    chmeo
    co
    wcel
    wa
    vc
    @3
    wral
    wa
    vs
    cC
    cpw
    c0
    csn
    cdif
    crab
    cmpt
    #
    vf
    vg
    va
    cF
    cG
    va
    cY
    cc0
    @5
    cfv
    #
    cO
    wceq
    #
    c1
    @5
    cfv
    #
    va
    cv
    #
    wceq
    #
    c1
    cF
    @6
    ccom
    #
    cG
    @5
    ccom
    #
    wceq
    #
    cc0
    @6
    cfv
    #
    cP
    wceq
    #
    wa
    #
    vd
    cii
    cC
    ccn
    co
    #
    crio
    #
    cfv
    #
    vb
    cv
    #
    wceq
    #
    w3a
    #
    vc
    cii
    cK
    ccn
    co
    #
    wrex
    #
    vb
    cB
    crio
    #
    cmpt
    cJ
    cK
    cO
    cY
    vb
    vv
    vu
    cvmlift3.b
    cvmlift3.y
    cvmlift3.f
    cvmlift3.k
    cvmlift3.l
    cvmlift3.o
    cvmlift3.g
    cvmlift3.p
    cvmlift3.e
    va
    vx
    cY
    @27
    cc0
    @0
    cfv
    #
    cO
    wceq
    #
    c1
    @0
    cfv
    #
    vx
    cv
    #
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
    @0
    ccom
    #
    wceq
    #
    cc0
    @33
    cfv
    #
    cP
    wceq
    #
    wa
    #
    vg
    @19
    crio
    #
    cfv
    #
    vz
    cv
    #
    wceq
    #
    w3a
    #
    vf
    @25
    wrex
    #
    vz
    cB
    crio
    #
    va
    vx
    weq
    #
    @27
    @9
    @12
    @21
    @42
    wceq
    #
    w3a
    #
    vc
    @25
    wrex
    #
    vz
    cB
    crio
    @46
    @26
    @50
    vb
    vz
    cB
    vb
    vz
    weq
    #
    @24
    @49
    vc
    @25
    @51
    @23
    @48
    @9
    @12
    @22
    @42
    @21
    eqeq2
    3anbi3d
    rexbidv
    cbvriotav
    @47
    @50
    @45
    vz
    cB
    @50
    @29
    @30
    @11
    wceq
    #
    @43
    w3a
    #
    vf
    @25
    wrex
    @47
    @45
    @49
    @53
    vc
    vf
    @25
    vc
    vf
    weq
    #
    @9
    @29
    @12
    @52
    @48
    @43
    @54
    @8
    @28
    cO
    cc0
    @5
    @0
    fveq1
    eqeq1d
    @54
    @10
    @30
    @11
    c1
    @5
    @0
    fveq1
    eqeq1d
    @54
    @21
    @41
    @42
    @54
    c1
    @20
    @40
    @54
    @20
    @34
    @14
    wceq
    #
    @38
    wa
    #
    vg
    @19
    crio
    @40
    @18
    @56
    vd
    vg
    @19
    vd
    vg
    weq
    #
    @15
    @55
    @17
    @38
    @57
    @13
    @34
    @14
    @6
    @33
    cF
    coeq2
    eqeq1d
    @57
    @16
    @37
    cP
    cc0
    @6
    @33
    fveq1
    eqeq1d
    anbi12d
    cbvriotav
    @54
    @56
    @39
    vg
    @19
    @54
    @55
    @36
    @38
    @54
    @14
    @35
    @34
    @5
    @0
    cG
    coeq2
    eqeq2d
    anbi1d
    riotabidv
    syl5eq
    fveq1d
    eqeq1d
    3anbi123d
    cbvrexv
    @47
    @53
    @44
    vf
    @25
    @47
    @52
    @32
    @29
    @43
    @11
    @31
    @30
    eqeq2
    3anbi2d
    rexbidv
    syl5bb
    riotabidv
    syl5eq
    cbvmptv
    vd
    vc
    cC
    @7
    vk
    cF
    cJ
    vs
    va
    vb
    vv
    vu
    @7
    eqid
    cvmscbv
    cvmlift3lem9
    wph
    cB
    cC
    cP
    vf
    cF
    cG
    cJ
    cK
    cO
    cY
    cvmlift3.b
    cvmlift3.y
    cvmlift3.f
    wph
    cK
    csconn
    wcel
    cK
    cpconn
    wcel
    cK
    cconn
    wcel
    cvmlift3.k
    cK
    sconnpconn
    cK
    pconnconn
    3syl
    wph
    cpconn
    cnlly
    #
    cconn
    cnlly
    #
    cK
    cpconn
    cconn
    wss
    @58
    @59
    wss
    vx
    cpconn
    cconn
    @31
    pconnconn
    ssriv
    cpconn
    cconn
    nllyss
    ax-mp
    cvmlift3.l
    sseldi
    cvmlift3.o
    cvmlift3.g
    cvmlift3.p
    cvmlift3.e
    cvmliftmo
    @1
    vf
    @2
    reu5
    sylanbrc
end
