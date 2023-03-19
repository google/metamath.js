include "w-bnj15.mm"
include "wcel.mm"
include "wa.mm"
include "c-bnj14.mm"
include "cvv.mm"
include "wi.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "elisset.mm"
include "adantl.mm"
include "bnj93.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "bnj602.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "mpbii.mm"
include "bnj593.mm"
include "bnj937.mm"
include "pm2.43i.mm"

theorem bnj1148
  let cA: class A
  let cR: class R
  let cX: class X
  let vx: setvar x


  assert |- ( ( R _FrSe A /\ X e. A ) -> _pred ( X , A , R ) e. _V )

  proof
    cA
    cR
    w-bnj15
    #
    cX
    cA
    wcel
    #
    wa
    #
    cA
    cR
    cX
    c-bnj14
    #
    cvv
    wcel
    #
    @2
    @2
    @4
    wi
    #
    vx
    @2
    vx
    cv
    #
    cX
    wceq
    #
    @5
    vx
    @1
    @7
    vx
    wex
    @0
    vx
    cX
    cA
    elisset
    adantl
    @7
    @0
    @6
    cA
    wcel
    #
    wa
    #
    cA
    cR
    @6
    c-bnj14
    #
    cvv
    wcel
    #
    wi
    @5
    vx
    cA
    cR
    bnj93
    @7
    @9
    @2
    @11
    @4
    @7
    @8
    @1
    @0
    @6
    cX
    cA
    eleq1
    anbi2d
    @7
    @10
    @3
    cvv
    cA
    cR
    @6
    cX
    bnj602
    eleq1d
    imbi12d
    mpbii
    bnj593
    bnj937
    pm2.43i
end
