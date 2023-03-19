include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cc0.mm"
include "cv.mm"
include "ccom.mm"
include "wa.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "crio.mm"
include "w3a.mm"
include "wrex.mm"
include "cpco.mm"
include "wcel.mm"
include "crest.mm"
include "ctop.mm"
include "wss.mm"
include "csconn.mm"
include "sconntop.mm"
include "syl.mm"
include "cnrest2r.mm"
include "sseldd.mm"
include "simp2d.mm"
include "simpld.mm"
include "eqtr4d.mm"
include "pcocn.mm"
include "pco0.mm"
include "simp1d.mm"
include "eqtrd.mm"
include "pco1.mm"
include "simprd.mm"
include "cnco.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "cicc.mm"
include "wf.mm"
include "iiuni.mm"
include "cnf.mm"
include "0elunit.mm"
include "fvco3.mm"
include "sylancl.mm"
include "3eqtr4rd.mm"
include "cvmliftiota.mm"
include "cvmlift3lem3.mm"
include "ccnv.mm"
include "cima.mm"
include "cdm.mm"
include "cnvimass.mm"
include "cuni.mm"
include "eqid.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "sstrd.mm"
include "ffvelrnd.mm"
include "cvmlift3lem5.mm"
include "fveq1d.mm"
include "eqtr3d.mm"
include "oveq12d.mm"
include "simp3d.mm"
include "ccvm.mm"
include "cvmcn.mm"
include "copco.mm"
include "3eqtr4d.mm"
include "wreu.mm"
include "wb.mm"
include "cvmlift.mm"
include "syl22anc.mm"
include "coeq2.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "anbi12d.mm"
include "riota2.mm"
include "mpbi2and.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "riotabidv.mm"
include "3anbi123d.mm"
include "rspcev.mm"
include "syl13anc.mm"
include "cvmlift3lem4.mm"
include "mpdan.mm"
include "mpbird.mm"
include "cconn.mm"
include "iiconn.mm"
include "a1i.mm"
include "ctopon.mm"
include "crn.mm"
include "cvmtop1.mm"
include "toptopon.mm"
include "sylib.mm"
include "rneqd.mm"
include "rnco2.mm"
include "3eqtr3g.mm"
include "iitopon.mm"
include "resttopon.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "frn.mm"
include "wfun.mm"
include "ffun.mm"
include "syl6ss.mm"
include "funimass3.mm"
include "eqsstrd.mm"
include "sseqtr4d.mm"
include "mpbid.mm"
include "cnrest2.mm"
include "cvmsss.mm"
include "eqeltrd.mm"
include "cvmsiota.mm"
include "elssuni.mm"
include "cvmsuni.mm"
include "sseqtrd.mm"
include "cvmsrcl.mm"
include "cnima.mm"
include "restopn2.mm"
include "mpbir2and.mm"
include "ccld.mm"
include "cvmscld.mm"
include "conncn.mm"
include "1elunit.mm"
include "ffvelrn.mm"

theorem cvmlift3lem6
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vw: setvar w
  let va: setvar a
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vh: setvar h
  let vn: setvar n
  let vm: setvar m
  let vt: setvar t
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
  assume cvmlift3lem6.x: |- ( ph -> X e. M )
  assume cvmlift3lem6.z: |- ( ph -> Z e. M )
  assume cvmlift3lem6.q: |- ( ph -> Q e. ( II Cn K ) )
  assume cvmlift3lem6.r: |- R = ( iota_ g e. ( II Cn C ) ( ( F o. g ) = ( G o. Q ) /\ ( g ` 0 ) = P ) )
  assume cvmlift3lem6.1: |- ( ph -> ( ( Q ` 0 ) = O /\ ( Q ` 1 ) = X /\ ( R ` 1 ) = ( H ` X ) ) )
  assume cvmlift3lem6.n: |- ( ph -> N e. ( II Cn ( K |`t M ) ) )
  assume cvmlift3lem6.2: |- ( ph -> ( ( N ` 0 ) = X /\ ( N ` 1 ) = Z ) )
  assume cvmlift3lem6.i: |- I = ( iota_ g e. ( II Cn C ) ( ( F o. g ) = ( G o. N ) /\ ( g ` 0 ) = ( H ` X ) ) )

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
  disjoint I f
  disjoint g z
  disjoint I g
  disjoint I z
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
  disjoint N f
  disjoint N g
  disjoint H b
  disjoint H c
  disjoint H d
  disjoint H f
  disjoint H g
  disjoint H x
  disjoint H z
  disjoint Q f
  disjoint Q g
  disjoint S b
  disjoint S f
  disjoint S x
  disjoint B b
  disjoint B d
  disjoint B f
  disjoint B g
  disjoint B x
  disjoint B z
  disjoint R g
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
  disjoint Z f
  disjoint Z g
  disjoint Z x
  disjoint Z z
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
  disjoint g w
  disjoint I w
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
  assert |- ( ph -> ( H ` Z ) e. W )

  proof
    wph
    cZ
    cH
    cfv
    #
    c1
    cI
    cfv
    #
    cW
    wph
    @0
    @1
    wceq
    #
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
    @3
    cfv
    #
    cZ
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
    @3
    ccom
    #
    wceq
    #
    cc0
    @8
    cfv
    #
    cP
    wceq
    #
    wa
    #
    vg
    cii
    cC
    ccn
    co
    #
    crio
    #
    cfv
    #
    @1
    wceq
    #
    w3a
    #
    vf
    cii
    cK
    ccn
    co
    #
    wrex
    #
    wph
    cQ
    cN
    cK
    cpco
    cfv
    co
    #
    @20
    wcel
    #
    cc0
    @22
    cfv
    #
    cO
    wceq
    #
    c1
    @22
    cfv
    #
    cZ
    wceq
    #
    c1
    @9
    cG
    @22
    ccom
    #
    wceq
    #
    @13
    wa
    #
    vg
    @15
    crio
    #
    cfv
    #
    @1
    wceq
    #
    @21
    wph
    cQ
    cN
    cK
    cvmlift3lem6.q
    wph
    cii
    cK
    cM
    crest
    co
    #
    ccn
    co
    #
    @20
    cN
    wph
    cK
    ctop
    wcel
    #
    @35
    @20
    wss
    wph
    cK
    csconn
    wcel
    @36
    cvmlift3.k
    cK
    sconntop
    syl
    #
    cM
    cii
    cK
    cnrest2r
    syl
    cvmlift3lem6.n
    sseldd
    #
    wph
    c1
    cQ
    cfv
    #
    cX
    cc0
    cN
    cfv
    #
    wph
    cc0
    cQ
    cfv
    #
    cO
    wceq
    #
    @39
    cX
    wceq
    #
    c1
    cR
    cfv
    #
    cX
    cH
    cfv
    #
    wceq
    #
    cvmlift3lem6.1
    simp2d
    wph
    @40
    cX
    wceq
    #
    c1
    cN
    cfv
    #
    cZ
    wceq
    #
    cvmlift3lem6.2
    simpld
    #
    eqtr4d
    #
    pcocn
    #
    wph
    @24
    @41
    cO
    wph
    cQ
    cN
    cK
    cvmlift3lem6.q
    @38
    pco0
    wph
    @42
    @43
    @46
    cvmlift3lem6.1
    simp1d
    #
    eqtrd
    #
    wph
    @26
    @48
    cZ
    wph
    cQ
    cN
    cK
    cvmlift3lem6.q
    @38
    pco1
    wph
    @47
    @49
    cvmlift3lem6.2
    simprd
    eqtrd
    wph
    @32
    c1
    cR
    cI
    cC
    cpco
    cfv
    co
    #
    cfv
    @1
    wph
    c1
    @31
    @55
    wph
    cF
    @55
    ccom
    #
    @28
    wceq
    #
    cc0
    @55
    cfv
    #
    cP
    wceq
    #
    @31
    @55
    wceq
    #
    wph
    cF
    cR
    ccom
    #
    cF
    cI
    ccom
    #
    cJ
    cpco
    cfv
    #
    co
    cG
    cQ
    ccom
    #
    cG
    cN
    ccom
    #
    @63
    co
    @56
    @28
    wph
    @61
    @64
    @62
    @65
    @63
    wph
    cR
    @15
    wcel
    #
    @61
    @64
    wceq
    #
    cc0
    cR
    cfv
    #
    cP
    wceq
    #
    wph
    cB
    cC
    cP
    vg
    cF
    @64
    cR
    cJ
    cvmlift3.b
    cvmlift3lem6.r
    cvmlift3.f
    wph
    cQ
    @20
    wcel
    #
    cG
    cK
    cJ
    ccn
    co
    wcel
    #
    @64
    cii
    cJ
    ccn
    co
    #
    wcel
    cvmlift3lem6.q
    cvmlift3.g
    cQ
    cG
    cii
    cK
    cJ
    cnco
    syl2anc
    cvmlift3.p
    wph
    @41
    cG
    cfv
    #
    cO
    cG
    cfv
    #
    cc0
    @64
    cfv
    #
    cP
    cF
    cfv
    #
    wph
    @41
    cO
    cG
    @53
    fveq2d
    wph
    cc0
    c1
    cicc
    co
    #
    cY
    cQ
    wf
    #
    cc0
    @77
    wcel
    #
    @75
    @73
    wceq
    wph
    @70
    @78
    cvmlift3lem6.q
    cQ
    cii
    cK
    @77
    cY
    iiuni
    cvmlift3.y
    cnf
    syl
    0elunit
    @77
    cY
    cc0
    cG
    cQ
    fvco3
    sylancl
    cvmlift3.e
    3eqtr4rd
    cvmliftiota
    #
    simp2d
    wph
    cI
    @15
    wcel
    #
    @62
    @65
    wceq
    #
    cc0
    cI
    cfv
    #
    @45
    wceq
    #
    wph
    cB
    cC
    @45
    vg
    cF
    @65
    cI
    cJ
    cvmlift3.b
    cvmlift3lem6.i
    cvmlift3.f
    wph
    cN
    @20
    wcel
    #
    @71
    @65
    @72
    wcel
    @38
    cvmlift3.g
    cN
    cG
    cii
    cK
    cJ
    cnco
    syl2anc
    wph
    cY
    cB
    cX
    cH
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
    @87
    cY
    cG
    cA
    cnvimass
    #
    wph
    cY
    cJ
    cuni
    #
    cG
    wf
    #
    @88
    cY
    wceq
    wph
    @71
    @91
    cvmlift3.g
    cG
    cK
    cJ
    cY
    @90
    cvmlift3.y
    @90
    eqid
    #
    cnf
    syl
    #
    cY
    @90
    cG
    fdm
    syl
    syl5sseq
    sstrd
    #
    cvmlift3lem6.x
    sseldd
    #
    ffvelrnd
    #
    wph
    @40
    cG
    cfv
    #
    cX
    cG
    cfv
    #
    cc0
    @65
    cfv
    #
    @45
    cF
    cfv
    #
    wph
    @40
    cX
    cG
    @50
    fveq2d
    wph
    @77
    cY
    cN
    wf
    #
    @79
    @99
    @97
    wceq
    wph
    @85
    @101
    @38
    cN
    cii
    cK
    @77
    cY
    iiuni
    cvmlift3.y
    cnf
    syl
    0elunit
    @77
    cY
    cc0
    cG
    cN
    fvco3
    sylancl
    wph
    cX
    cF
    cH
    ccom
    #
    cfv
    #
    @100
    @98
    wph
    cY
    cB
    cH
    wf
    cX
    cY
    wcel
    @103
    @100
    wceq
    @86
    @95
    cY
    cB
    cX
    cF
    cH
    fvco3
    syl2anc
    wph
    cX
    @102
    cG
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
    fveq1d
    eqtr3d
    #
    3eqtr4rd
    cvmliftiota
    #
    simp2d
    #
    oveq12d
    wph
    cR
    cI
    cF
    cC
    cJ
    wph
    @66
    @67
    @69
    @80
    simp1d
    #
    wph
    @81
    @82
    @84
    @105
    simp1d
    #
    wph
    @44
    @45
    @83
    wph
    @42
    @43
    @46
    cvmlift3lem6.1
    simp3d
    wph
    @81
    @82
    @84
    @105
    simp3d
    #
    eqtr4d
    #
    wph
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    cF
    cC
    cJ
    ccn
    co
    wcel
    #
    cvmlift3.f
    cC
    cF
    cJ
    cvmcn
    syl
    #
    copco
    wph
    cQ
    cN
    cG
    cK
    cJ
    cvmlift3lem6.q
    @38
    @51
    cvmlift3.g
    copco
    3eqtr4d
    wph
    @58
    @68
    cP
    wph
    cR
    cI
    cC
    @107
    @108
    pco0
    wph
    @66
    @67
    @69
    @80
    simp3d
    eqtrd
    wph
    @55
    @15
    wcel
    @30
    vg
    @15
    wreu
    #
    @57
    @59
    wa
    #
    @60
    wb
    wph
    cR
    cI
    cC
    @107
    @108
    @110
    pcocn
    wph
    @111
    @28
    @72
    wcel
    #
    cP
    cB
    wcel
    @76
    cc0
    @28
    cfv
    #
    wceq
    @114
    cvmlift3.f
    wph
    @23
    @71
    @116
    @52
    cvmlift3.g
    @22
    cG
    cii
    cK
    cJ
    cnco
    syl2anc
    cvmlift3.p
    wph
    @24
    cG
    cfv
    #
    @74
    @117
    @76
    wph
    @24
    cO
    cG
    @54
    fveq2d
    wph
    @77
    cY
    @22
    wf
    #
    @79
    @117
    @118
    wceq
    wph
    @23
    @119
    @52
    @22
    cii
    cK
    @77
    cY
    iiuni
    cvmlift3.y
    cnf
    syl
    0elunit
    @77
    cY
    cc0
    cG
    @22
    fvco3
    sylancl
    cvmlift3.e
    3eqtr4rd
    cB
    cC
    cP
    vg
    cF
    @28
    cJ
    cvmlift3.b
    cvmlift
    syl22anc
    @30
    @115
    vg
    @15
    @55
    @8
    @55
    wceq
    #
    @29
    @57
    @13
    @59
    @120
    @9
    @56
    @28
    @8
    @55
    cF
    coeq2
    eqeq1d
    @120
    @12
    @58
    cP
    cc0
    @8
    @55
    fveq1
    eqeq1d
    anbi12d
    riota2
    syl2anc
    mpbi2and
    fveq1d
    wph
    cR
    cI
    cC
    @107
    @108
    pco1
    eqtrd
    @19
    @25
    @27
    @33
    w3a
    vf
    @22
    @20
    @3
    @22
    wceq
    #
    @5
    @25
    @7
    @27
    @18
    @33
    @121
    @4
    @24
    cO
    cc0
    @3
    @22
    fveq1
    eqeq1d
    @121
    @6
    @26
    cZ
    c1
    @3
    @22
    fveq1
    eqeq1d
    @121
    @17
    @32
    @1
    @121
    c1
    @16
    @31
    @121
    @14
    @30
    vg
    @15
    @121
    @11
    @29
    @13
    @121
    @10
    @28
    @9
    @3
    @22
    cG
    coeq2
    eqeq2d
    anbi1d
    riotabidv
    fveq1d
    eqeq1d
    3anbi123d
    rspcev
    syl13anc
    wph
    cZ
    cY
    wcel
    @2
    @21
    wb
    wph
    cM
    cY
    cZ
    @94
    cvmlift3lem6.z
    sseldd
    wph
    vx
    vz
    @1
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
    cZ
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
    mpdan
    mpbird
    wph
    @77
    cW
    cI
    wf
    c1
    @77
    wcel
    @1
    cW
    wcel
    wph
    cc0
    cW
    cI
    cii
    cC
    cF
    ccnv
    cA
    cima
    #
    crest
    co
    #
    @77
    iiuni
    cii
    cconn
    wcel
    wph
    iiconn
    a1i
    wph
    @81
    cI
    cii
    @123
    ccn
    co
    wcel
    #
    @108
    wph
    cC
    cB
    ctopon
    cfv
    wcel
    #
    cI
    crn
    #
    @122
    wss
    #
    @122
    cB
    wss
    @81
    @124
    wb
    wph
    cC
    ctop
    wcel
    #
    @125
    wph
    @111
    @128
    cvmlift3.f
    cC
    cF
    cJ
    cvmtop1
    syl
    #
    cC
    cB
    cvmlift3.b
    toptopon
    sylib
    wph
    cF
    @126
    cima
    #
    cA
    wss
    #
    @127
    wph
    @130
    cG
    cN
    crn
    #
    cima
    #
    cA
    wph
    @62
    crn
    @65
    crn
    @130
    @133
    wph
    @62
    @65
    @106
    rneqd
    cF
    cI
    rnco2
    cG
    cN
    rnco2
    3eqtr3g
    wph
    @133
    cA
    wss
    #
    @132
    @87
    wss
    #
    wph
    @132
    cM
    @87
    wph
    @77
    cM
    cN
    wf
    #
    @132
    cM
    wss
    wph
    cii
    @77
    ctopon
    cfv
    wcel
    #
    @34
    cM
    ctopon
    cfv
    wcel
    #
    cN
    @35
    wcel
    @136
    @137
    wph
    iitopon
    a1i
    wph
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cM
    cY
    wss
    @138
    wph
    @36
    @139
    @37
    cK
    cY
    cvmlift3.y
    toptopon
    sylib
    @94
    cM
    cK
    cY
    resttopon
    syl2anc
    cvmlift3lem6.n
    cN
    cii
    @34
    @77
    cM
    cnf2
    syl3anc
    @77
    cM
    cN
    frn
    syl
    cvmlift3lem7.3
    sstrd
    #
    wph
    cG
    wfun
    #
    @132
    @88
    wss
    @134
    @135
    wb
    wph
    @91
    @141
    @93
    cY
    @90
    cG
    ffun
    syl
    wph
    @132
    @87
    @88
    @140
    @89
    syl6ss
    @132
    cA
    cG
    funimass3
    syl2anc
    mpbird
    eqsstrd
    wph
    cF
    wfun
    #
    @126
    cF
    cdm
    #
    wss
    @131
    @127
    wb
    wph
    cB
    @90
    cF
    wf
    #
    @142
    wph
    @112
    @144
    @113
    cF
    cC
    cJ
    cB
    @90
    cvmlift3.b
    @92
    cnf
    syl
    #
    cB
    @90
    cF
    ffun
    syl
    wph
    @126
    cB
    @143
    wph
    @77
    cB
    cI
    wf
    #
    @126
    cB
    wss
    wph
    @81
    @146
    @108
    cI
    cii
    cC
    @77
    cB
    iiuni
    cvmlift3.b
    cnf
    syl
    @77
    cB
    cI
    frn
    syl
    wph
    @144
    @143
    cB
    wceq
    @145
    cB
    @90
    cF
    fdm
    syl
    #
    sseqtr4d
    @126
    cA
    cF
    funimass3
    syl2anc
    mpbid
    wph
    @143
    @122
    cB
    cF
    cA
    cnvimass
    @147
    syl5sseq
    @122
    cI
    cii
    cC
    cB
    cnrest2
    syl3anc
    mpbid
    wph
    cW
    @123
    wcel
    #
    cW
    cC
    wcel
    #
    cW
    @122
    wss
    #
    wph
    cT
    cC
    cW
    wph
    cT
    cA
    cS
    cfv
    wcel
    #
    cT
    cC
    wss
    cvmlift3lem7.2
    vd
    vc
    cC
    cS
    cT
    cA
    vk
    cF
    cJ
    vs
    cvmlift3lem7.s
    cvmsss
    syl
    wph
    cW
    cT
    wcel
    #
    @45
    cW
    wcel
    #
    wph
    @111
    @151
    @45
    cB
    wcel
    @100
    cA
    wcel
    @152
    @153
    wa
    cvmlift3.f
    cvmlift3lem7.2
    @96
    wph
    @100
    @98
    cA
    @104
    cvmlift3lem7.1
    eqeltrd
    vb
    vd
    vc
    @45
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
    #
    simpld
    #
    sseldd
    wph
    cW
    cT
    cuni
    #
    @122
    wph
    @152
    cW
    @156
    wss
    @155
    cW
    cT
    elssuni
    syl
    wph
    @151
    @156
    @122
    wceq
    cvmlift3lem7.2
    vd
    vc
    cC
    cS
    cT
    cA
    vk
    cF
    cJ
    vs
    cvmlift3lem7.s
    cvmsuni
    syl
    sseqtrd
    wph
    @128
    @122
    cC
    wcel
    #
    @148
    @149
    @150
    wa
    wb
    @129
    wph
    @112
    cA
    cJ
    wcel
    #
    @157
    @113
    wph
    @151
    @158
    cvmlift3lem7.2
    vd
    vc
    cC
    cS
    cT
    cA
    vk
    cF
    cJ
    vs
    cvmlift3lem7.s
    cvmsrcl
    syl
    cA
    cF
    cC
    cJ
    cnima
    syl2anc
    @122
    cW
    cC
    restopn2
    syl2anc
    mpbir2and
    wph
    @111
    @151
    @152
    cW
    @123
    ccld
    cfv
    wcel
    cvmlift3.f
    cvmlift3lem7.2
    @155
    vd
    vc
    cW
    cC
    cS
    cT
    cA
    vk
    cF
    cJ
    vs
    cvmlift3lem7.s
    cvmscld
    syl3anc
    @79
    wph
    0elunit
    a1i
    wph
    @83
    @45
    cW
    @109
    wph
    @152
    @153
    @154
    simprd
    eqeltrd
    conncn
    1elunit
    @77
    cW
    c1
    cI
    ffvelrn
    sylancl
    eqeltrd
end
