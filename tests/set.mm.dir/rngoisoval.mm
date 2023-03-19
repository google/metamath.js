include "crngo.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "crn.mm"
include "wf1o.mm"
include "crnghom.mm"
include "co.mm"
include "crab.mm"
include "crngiso.mm"
include "wceq.mm"
include "wa.mm"
include "oveq12.mm"
include "wb.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "f1oeq2.mm"
include "syl.mm"
include "f1oeq3.mm"
include "sylan9bb.mm"
include "rabeqbidv.mm"
include "df-rngoiso.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2a.mm"

theorem rngoisoval
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cG: class G
  let cJ: class J
  let cX: class X
  let cY: class Y
  let cF: class F
  let vr: setvar r
  let vs: setvar s
  assume rngisoval.1: |- G = ( 1st ` R )
  assume rngisoval.2: |- X = ran G
  assume rngisoval.3: |- J = ( 1st ` S )
  assume rngisoval.4: |- Y = ran J

  disjoint R f
  disjoint S f
  disjoint X f
  disjoint Y f
  disjoint F f
  disjoint f r
  disjoint f s
  disjoint r s
  disjoint R r
  disjoint R s
  disjoint S r
  disjoint S s
  disjoint X r
  disjoint X s
  disjoint Y r
  disjoint Y s
  assert |- ( ( R e. RingOps /\ S e. RingOps ) -> ( R RngIso S ) = { f e. ( R RngHom S ) | f : X -1-1-onto-> Y } )

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
    c1st
    cfv
    #
    crn
    #
    vs
    cv
    #
    c1st
    cfv
    #
    crn
    #
    vf
    cv
    #
    wf1o
    #
    vf
    @0
    @3
    crnghom
    co
    #
    crab
    cX
    cY
    @6
    wf1o
    #
    vf
    cR
    cS
    crnghom
    co
    #
    crab
    crngiso
    @0
    cR
    wceq
    #
    @3
    cS
    wceq
    #
    wa
    @7
    @9
    vf
    @8
    @10
    @0
    cR
    @3
    cS
    crnghom
    oveq12
    @11
    @7
    cX
    @5
    @6
    wf1o
    #
    @12
    @9
    @11
    @2
    cX
    wceq
    @7
    @13
    wb
    @11
    @2
    cG
    crn
    cX
    @11
    @1
    cG
    @11
    @1
    cR
    c1st
    cfv
    cG
    @0
    cR
    c1st
    fveq2
    rngisoval.1
    syl6eqr
    rneqd
    rngisoval.2
    syl6eqr
    @2
    cX
    @5
    @6
    f1oeq2
    syl
    @12
    @5
    cY
    wceq
    @13
    @9
    wb
    @12
    @5
    cJ
    crn
    cY
    @12
    @4
    cJ
    @12
    @4
    cS
    c1st
    cfv
    cJ
    @3
    cS
    c1st
    fveq2
    rngisoval.3
    syl6eqr
    rneqd
    rngisoval.4
    syl6eqr
    @5
    cY
    cX
    @6
    f1oeq3
    syl
    sylan9bb
    rabeqbidv
    vf
    vs
    vr
    df-rngoiso
    @9
    vf
    @10
    cR
    cS
    crnghom
    ovex
    rabex
    ovmpt2a
end
