include "crngo.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "cgi.mm"
include "wceq.mm"
include "c1st.mm"
include "co.mm"
include "wa.mm"
include "crn.mm"
include "wral.mm"
include "cmap.mm"
include "crab.mm"
include "crnghom.mm"
include "simpr.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "simpl.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "oveqd.mm"
include "anbi12d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "df-rngohom.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2a.mm"

theorem rngohomval
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cS: class S
  let cU: class U
  let vf: setvar f
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let cF: class F
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

  disjoint f x
  disjoint f y
  disjoint x y
  disjoint G f
  disjoint H f
  disjoint J f
  disjoint Y f
  disjoint Y y
  disjoint K f
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint S f
  disjoint S x
  disjoint S y
  disjoint X f
  disjoint X x
  disjoint X y
  disjoint U f
  disjoint V f
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint f r
  disjoint f s
  disjoint r s
  disjoint G r
  disjoint G s
  disjoint H r
  disjoint H s
  disjoint J r
  disjoint J s
  disjoint r y
  disjoint Y r
  disjoint s y
  disjoint Y s
  disjoint K r
  disjoint K s
  disjoint r x
  disjoint R r
  disjoint s x
  disjoint R s
  disjoint S r
  disjoint S s
  disjoint X r
  disjoint X s
  disjoint U r
  disjoint U s
  disjoint V r
  disjoint V s
  assert |- ( ( R e. RingOps /\ S e. RingOps ) -> ( R RngHom S ) = { f e. ( Y ^m X ) | ( ( f ` U ) = V /\ A. x e. X A. y e. X ( ( f ` ( x G y ) ) = ( ( f ` x ) J ( f ` y ) ) /\ ( f ` ( x H y ) ) = ( ( f ` x ) K ( f ` y ) ) ) ) } )

  proof
    vr
    vs
    cR
    cS
    crngo
    crngo
    vr
    cv
    #
    c2nd
    cfv
    #
    cgi
    cfv
    #
    vf
    cv
    #
    cfv
    #
    vs
    cv
    #
    c2nd
    cfv
    #
    cgi
    cfv
    #
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    @0
    c1st
    cfv
    #
    co
    #
    @3
    cfv
    #
    @9
    @3
    cfv
    #
    @10
    @3
    cfv
    #
    @5
    c1st
    cfv
    #
    co
    #
    wceq
    #
    @9
    @10
    @1
    co
    #
    @3
    cfv
    #
    @14
    @15
    @6
    co
    #
    wceq
    #
    wa
    #
    vy
    @11
    crn
    #
    wral
    #
    vx
    @24
    wral
    #
    wa
    #
    vf
    @16
    crn
    #
    @24
    cmap
    co
    #
    crab
    cU
    @3
    cfv
    #
    cV
    wceq
    #
    @9
    @10
    cG
    co
    #
    @3
    cfv
    #
    @14
    @15
    cJ
    co
    #
    wceq
    #
    @9
    @10
    cH
    co
    #
    @3
    cfv
    #
    @14
    @15
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
    #
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
    crnghom
    @0
    cR
    wceq
    #
    @5
    cS
    wceq
    #
    wa
    #
    @27
    @43
    vf
    @29
    @44
    @47
    @28
    cY
    @24
    cX
    cmap
    @47
    @28
    cJ
    crn
    cY
    @47
    @16
    cJ
    @47
    @16
    cS
    c1st
    cfv
    cJ
    @47
    @5
    cS
    c1st
    @45
    @46
    simpr
    #
    fveq2d
    rnghomval.5
    syl6eqr
    #
    rneqd
    rnghomval.7
    syl6eqr
    @47
    @24
    cG
    crn
    cX
    @47
    @11
    cG
    @47
    @11
    cR
    c1st
    cfv
    cG
    @47
    @0
    cR
    c1st
    @45
    @46
    simpl
    #
    fveq2d
    rnghomval.1
    syl6eqr
    #
    rneqd
    rnghomval.3
    syl6eqr
    #
    oveq12d
    @47
    @8
    @31
    @26
    @42
    @47
    @4
    @30
    @7
    cV
    @47
    @2
    cU
    @3
    @47
    @2
    cH
    cgi
    cfv
    cU
    @47
    @1
    cH
    cgi
    @47
    @1
    cR
    c2nd
    cfv
    cH
    @47
    @0
    cR
    c2nd
    @50
    fveq2d
    rnghomval.2
    syl6eqr
    #
    fveq2d
    rnghomval.4
    syl6eqr
    fveq2d
    @47
    @7
    cK
    cgi
    cfv
    cV
    @47
    @6
    cK
    cgi
    @47
    @6
    cS
    c2nd
    cfv
    cK
    @47
    @5
    cS
    c2nd
    @48
    fveq2d
    rnghomval.6
    syl6eqr
    #
    fveq2d
    rnghomval.8
    syl6eqr
    eqeq12d
    @47
    @25
    @41
    vx
    @24
    cX
    @52
    @47
    @23
    @40
    vy
    @24
    cX
    @52
    @47
    @18
    @35
    @22
    @39
    @47
    @13
    @33
    @17
    @34
    @47
    @12
    @32
    @3
    @47
    @11
    cG
    @9
    @10
    @51
    oveqd
    fveq2d
    @47
    @16
    cJ
    @14
    @15
    @49
    oveqd
    eqeq12d
    @47
    @20
    @37
    @21
    @38
    @47
    @19
    @36
    @3
    @47
    @1
    cH
    @9
    @10
    @53
    oveqd
    fveq2d
    @47
    @6
    cK
    @14
    @15
    @54
    oveqd
    eqeq12d
    anbi12d
    raleqbidv
    raleqbidv
    anbi12d
    rabeqbidv
    vx
    vy
    vf
    vs
    vr
    df-rngohom
    @43
    vf
    @44
    cY
    cX
    cmap
    ovex
    rabex
    ovmpt2a
end
