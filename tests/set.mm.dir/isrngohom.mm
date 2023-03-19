include "crngo.mm"
include "wcel.mm"
include "wa.mm"
include "crnghom.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cmap.mm"
include "crab.mm"
include "wf.mm"
include "w3a.mm"
include "rngohomval.mm"
include "eleq2d.mm"
include "crn.mm"
include "cvv.mm"
include "c1st.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rnex.mm"
include "elmap.mm"
include "anbi1i.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "2ralbidv.mm"
include "elrab.mm"
include "3anass.mm"
include "3bitr4i.mm"
include "syl6bb.mm"

theorem isrngohom
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  assume rnghomval.1: |- G = ( 1st ` R )
  assume rnghomval.2: |- H = ( 2nd ` R )
  assume rnghomval.3: |- X = ran G
  assume rnghomval.4: |- U = ( GId ` H )
  assume rnghomval.5: |- J = ( 1st ` S )
  assume rnghomval.6: |- K = ( 2nd ` S )
  assume rnghomval.7: |- Y = ran J
  assume rnghomval.8: |- V = ( GId ` K )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint Y y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint f r
  disjoint f s
  disjoint G f
  disjoint r s
  disjoint G r
  disjoint G s
  disjoint H f
  disjoint H r
  disjoint H s
  disjoint J f
  disjoint J r
  disjoint J s
  disjoint Y f
  disjoint r y
  disjoint Y r
  disjoint s y
  disjoint Y s
  disjoint K f
  disjoint K r
  disjoint K s
  disjoint R f
  disjoint r x
  disjoint R r
  disjoint s x
  disjoint R s
  disjoint S f
  disjoint S r
  disjoint S s
  disjoint X f
  disjoint X r
  disjoint X s
  disjoint U f
  disjoint U r
  disjoint U s
  disjoint V f
  disjoint V r
  disjoint V s
  assert |- ( ( R e. RingOps /\ S e. RingOps ) -> ( F e. ( R RngHom S ) <-> ( F : X --> Y /\ ( F ` U ) = V /\ A. x e. X A. y e. X ( ( F ` ( x G y ) ) = ( ( F ` x ) J ( F ` y ) ) /\ ( F ` ( x H y ) ) = ( ( F ` x ) K ( F ` y ) ) ) ) ) )

  proof
    cR
    crngo
    wcel
    cS
    crngo
    wcel
    wa
    #
    cF
    cR
    cS
    crnghom
    co
    #
    wcel
    cF
    cU
    vf
    cv
    #
    cfv
    #
    cV
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    #
    @2
    cfv
    #
    @5
    @2
    cfv
    #
    @6
    @2
    cfv
    #
    cJ
    co
    #
    wceq
    #
    @5
    @6
    cH
    co
    #
    @2
    cfv
    #
    @9
    @10
    cK
    co
    #
    wceq
    #
    wa
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    wa
    #
    vf
    cY
    cX
    cmap
    co
    #
    crab
    #
    wcel
    #
    cX
    cY
    cF
    wf
    #
    cU
    cF
    cfv
    #
    cV
    wceq
    #
    @7
    cF
    cfv
    #
    @5
    cF
    cfv
    #
    @6
    cF
    cfv
    #
    cJ
    co
    #
    wceq
    #
    @13
    cF
    cfv
    #
    @27
    @28
    cK
    co
    #
    wceq
    #
    wa
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    w3a
    #
    @0
    @1
    @21
    cF
    vx
    vy
    cR
    cS
    cU
    vf
    cG
    cH
    cJ
    cK
    cV
    cX
    cY
    rnghomval.1
    rnghomval.2
    rnghomval.3
    rnghomval.4
    rnghomval.5
    rnghomval.6
    rnghomval.7
    rnghomval.8
    rngohomval
    eleq2d
    cF
    @20
    wcel
    #
    @25
    @35
    wa
    #
    wa
    @23
    @38
    wa
    @22
    @36
    @37
    @23
    @38
    cY
    cX
    cF
    cY
    cJ
    crn
    cvv
    rnghomval.7
    cJ
    cJ
    cS
    c1st
    cfv
    cvv
    rnghomval.5
    cS
    c1st
    fvex
    eqeltri
    rnex
    eqeltri
    cX
    cG
    crn
    cvv
    rnghomval.3
    cG
    cG
    cR
    c1st
    cfv
    cvv
    rnghomval.1
    cR
    c1st
    fvex
    eqeltri
    rnex
    eqeltri
    elmap
    anbi1i
    @19
    @38
    vf
    cF
    @20
    @2
    cF
    wceq
    #
    @4
    @25
    @18
    @35
    @39
    @3
    @24
    cV
    cU
    @2
    cF
    fveq1
    eqeq1d
    @39
    @17
    @34
    vx
    vy
    cX
    cX
    @39
    @12
    @30
    @16
    @33
    @39
    @8
    @26
    @11
    @29
    @7
    @2
    cF
    fveq1
    @39
    @9
    @27
    @10
    @28
    cJ
    @5
    @2
    cF
    fveq1
    #
    @6
    @2
    cF
    fveq1
    #
    oveq12d
    eqeq12d
    @39
    @14
    @31
    @15
    @32
    @13
    @2
    cF
    fveq1
    @39
    @9
    @27
    @10
    @28
    cK
    @40
    @41
    oveq12d
    eqeq12d
    anbi12d
    2ralbidv
    anbi12d
    elrab
    @23
    @25
    @35
    3anass
    3bitr4i
    syl6bb
end
