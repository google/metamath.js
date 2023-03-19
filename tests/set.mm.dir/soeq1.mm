include "wceq.mm"
include "wpo.mm"
include "cv.mm"
include "wbr.mm"
include "w3o.mm"
include "wral.mm"
include "wa.mm"
include "wor.mm"
include "poeq1.mm"
include "breq.mm"
include "biidd.mm"
include "3orbi123d.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "df-so.mm"
include "3bitr4g.mm"

theorem soeq1
  let cA: class A
  let cR: class R
  let cS: class S
  let vx: setvar x
  let vy: setvar y


  assert |- ( R = S -> ( R Or A <-> S Or A ) )

  proof
    cR
    cS
    wceq
    #
    cA
    cR
    wpo
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @2
    @3
    wceq
    #
    @3
    @2
    cR
    wbr
    #
    w3o
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    cA
    cS
    wpo
    #
    @2
    @3
    cS
    wbr
    #
    @5
    @3
    @2
    cS
    wbr
    #
    w3o
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    cA
    cR
    wor
    cA
    cS
    wor
    @0
    @1
    @9
    @8
    @13
    cA
    cR
    cS
    poeq1
    @0
    @7
    @12
    vx
    vy
    cA
    cA
    @0
    @4
    @10
    @5
    @5
    @6
    @11
    @2
    @3
    cR
    cS
    breq
    @0
    @5
    biidd
    @3
    @2
    cR
    cS
    breq
    3orbi123d
    2ralbidv
    anbi12d
    vx
    vy
    cA
    cR
    df-so
    vx
    vy
    cA
    cS
    df-so
    3bitr4g
end
