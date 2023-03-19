include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "ccom.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "crio.mm"
include "w3a.mm"
include "wrex.mm"
include "eqid.mm"
include "cvmlift3lem4.mm"
include "mpbii.mm"
include "df-3an.mm"
include "ccvm.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "cnco.mm"
include "syl2anc.mm"
include "simprl.mm"
include "fveq2d.mm"
include "cicc.mm"
include "wf.mm"
include "iiuni.mm"
include "cnf.mm"
include "syl.mm"
include "0elunit.mm"
include "fvco3.mm"
include "sylancl.mm"
include "3eqtr4rd.mm"
include "cvmliftiota.mm"
include "simp2d.mm"
include "fveq1d.mm"
include "simp1d.mm"
include "1elunit.mm"
include "simprr.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "syl5ibcom.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "mpteq2dva.mm"
include "cvmlift3lem3.mm"
include "ffvelrnda.mm"
include "feqmptd.mm"
include "cuni.mm"
include "cvmcn.mm"
include "3syl.mm"
include "fmptco.mm"
include "3eqtr4d.mm"

theorem cvmlift3lem5
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cP: class P
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cH: class H
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
  let cA: class A
  let cI: class I
  let va: setvar a
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vh: setvar h
  let vn: setvar n
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vt: setvar t
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
  assume cvmlift3.h: |- H = ( x e. Y |-> ( iota_ z e. B E. f e. ( II Cn K ) ( ( f ` 0 ) = O /\ ( f ` 1 ) = x /\ ( ( iota_ g e. ( II Cn C ) ( ( F o. g ) = ( G o. f ) /\ ( g ` 0 ) = P ) ) ` 1 ) = z ) ) )

  disjoint f z
  disjoint f g
  disjoint g z
  disjoint f x
  disjoint J f
  disjoint g x
  disjoint J g
  disjoint J x
  disjoint F f
  disjoint F g
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint H f
  disjoint H g
  disjoint H x
  disjoint H z
  disjoint B f
  disjoint B g
  disjoint B x
  disjoint B z
  disjoint G f
  disjoint G g
  disjoint G x
  disjoint G z
  disjoint C f
  disjoint C g
  disjoint C x
  disjoint C z
  disjoint f ph
  disjoint ph x
  disjoint K f
  disjoint K g
  disjoint K x
  disjoint K z
  disjoint P f
  disjoint P g
  disjoint P x
  disjoint P z
  disjoint O f
  disjoint O g
  disjoint O x
  disjoint O z
  disjoint Y f
  disjoint Y g
  disjoint Y x
  disjoint Y z
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
  disjoint f y
  disjoint g k
  disjoint g s
  disjoint g u
  disjoint g v
  disjoint g y
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
  disjoint y z
  disjoint F y
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
  disjoint S b
  disjoint S f
  disjoint S m
  disjoint S t
  disjoint S v
  disjoint S x
  disjoint B a
  disjoint B b
  disjoint B d
  disjoint B h
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B y
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
  disjoint G y
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
  disjoint K b
  disjoint K c
  disjoint K h
  disjoint K m
  disjoint K n
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K y
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P d
  disjoint P h
  disjoint P n
  disjoint P u
  disjoint P v
  disjoint P w
  disjoint O a
  disjoint O b
  disjoint O c
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
  disjoint W c
  disjoint W d
  disjoint W f
  disjoint W h
  disjoint W n
  disjoint W x
  disjoint W y
  assert |- ( ph -> ( F o. H ) = G )

  proof
    wph
    vy
    cY
    vy
    cv
    #
    cH
    cfv
    #
    cF
    cfv
    #
    cmpt
    vy
    cY
    @0
    cG
    cfv
    #
    cmpt
    cF
    cH
    ccom
    cG
    wph
    vy
    cY
    @2
    @3
    wph
    @0
    cY
    wcel
    #
    wa
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
    @6
    cfv
    #
    @0
    wceq
    #
    c1
    cF
    vg
    cv
    #
    ccom
    cG
    @6
    ccom
    #
    wceq
    cc0
    @11
    cfv
    cP
    wceq
    wa
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
    @2
    @3
    wceq
    #
    @5
    @1
    @1
    wceq
    @19
    @1
    eqid
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
    @0
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
    @5
    @17
    @20
    vf
    @18
    @17
    @8
    @10
    wa
    #
    @16
    wa
    @5
    @6
    @18
    wcel
    #
    wa
    #
    @20
    @8
    @10
    @16
    df-3an
    @23
    @21
    @16
    @20
    @23
    @21
    wa
    #
    @15
    cF
    cfv
    #
    @3
    wceq
    @16
    @20
    @24
    c1
    cF
    @14
    ccom
    #
    cfv
    #
    c1
    @12
    cfv
    #
    @25
    @3
    @24
    c1
    @26
    @12
    @24
    @14
    @13
    wcel
    #
    @26
    @12
    wceq
    #
    cc0
    @14
    cfv
    cP
    wceq
    #
    @24
    cB
    cC
    cP
    vg
    cF
    @12
    @14
    cJ
    cvmlift3.b
    @14
    eqid
    wph
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    @4
    @22
    @21
    cvmlift3.f
    ad3antrrr
    @24
    @22
    cG
    cK
    cJ
    ccn
    co
    wcel
    #
    @12
    cii
    cJ
    ccn
    co
    wcel
    @5
    @22
    @21
    simplr
    #
    wph
    @33
    @4
    @22
    @21
    cvmlift3.g
    ad3antrrr
    @6
    cG
    cii
    cK
    cJ
    cnco
    syl2anc
    wph
    cP
    cB
    wcel
    @4
    @22
    @21
    cvmlift3.p
    ad3antrrr
    @24
    @7
    cG
    cfv
    #
    cO
    cG
    cfv
    #
    cc0
    @12
    cfv
    #
    cP
    cF
    cfv
    #
    @24
    @7
    cO
    cG
    @23
    @8
    @10
    simprl
    fveq2d
    @24
    cc0
    c1
    cicc
    co
    #
    cY
    @6
    wf
    #
    cc0
    @39
    wcel
    @37
    @35
    wceq
    @24
    @22
    @40
    @34
    @6
    cii
    cK
    @39
    cY
    iiuni
    cvmlift3.y
    cnf
    syl
    #
    0elunit
    @39
    cY
    cc0
    cG
    @6
    fvco3
    sylancl
    wph
    @38
    @36
    wceq
    @4
    @22
    @21
    cvmlift3.e
    ad3antrrr
    3eqtr4rd
    cvmliftiota
    #
    simp2d
    fveq1d
    @24
    @39
    cB
    @14
    wf
    #
    c1
    @39
    wcel
    #
    @27
    @25
    wceq
    @24
    @29
    @43
    @24
    @29
    @30
    @31
    @42
    simp1d
    @14
    cii
    cC
    @39
    cB
    iiuni
    cvmlift3.b
    cnf
    syl
    1elunit
    @39
    cB
    c1
    cF
    @14
    fvco3
    sylancl
    @24
    @28
    @9
    cG
    cfv
    #
    @3
    @24
    @40
    @44
    @28
    @45
    wceq
    @41
    1elunit
    @39
    cY
    c1
    cG
    @6
    fvco3
    sylancl
    @24
    @9
    @0
    cG
    @23
    @8
    @10
    simprr
    fveq2d
    eqtrd
    3eqtr3d
    @16
    @25
    @2
    @3
    @15
    @1
    cF
    fveq2
    eqeq1d
    syl5ibcom
    expimpd
    syl5bi
    rexlimdva
    mpd
    mpteq2dva
    wph
    vy
    vw
    cY
    cB
    @1
    vw
    cv
    #
    cF
    cfv
    @2
    cH
    cF
    wph
    cY
    cB
    @0
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
    ffvelrnda
    wph
    vy
    cY
    cB
    cH
    @47
    feqmptd
    wph
    vw
    cB
    cJ
    cuni
    #
    cF
    wph
    @32
    cF
    cC
    cJ
    ccn
    co
    wcel
    cB
    @48
    cF
    wf
    cvmlift3.f
    cC
    cF
    cJ
    cvmcn
    cF
    cC
    cJ
    cB
    @48
    cvmlift3.b
    @48
    eqid
    #
    cnf
    3syl
    feqmptd
    @46
    @1
    cF
    fveq2
    fmptco
    wph
    vy
    cY
    @48
    cG
    wph
    @33
    cY
    @48
    cG
    wf
    cvmlift3.g
    cG
    cK
    cJ
    cY
    @48
    cvmlift3.y
    @49
    cnf
    syl
    feqmptd
    3eqtr4d
end
