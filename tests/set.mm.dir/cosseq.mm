include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "ccoss.mm"
include "breq.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "opabbidv.mm"
include "df-coss.mm"
include "3eqtr4g.mm"

theorem cosseq
  let cA: class A
  let cB: class B
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y


  assert |- ( A = B -> ,~ A = ,~ B )

  proof
    cA
    cB
    wceq
    #
    vu
    cv
    #
    vx
    cv
    #
    cA
    wbr
    #
    @1
    vy
    cv
    #
    cA
    wbr
    #
    wa
    #
    vu
    wex
    #
    vx
    vy
    copab
    @1
    @2
    cB
    wbr
    #
    @1
    @4
    cB
    wbr
    #
    wa
    #
    vu
    wex
    #
    vx
    vy
    copab
    cA
    ccoss
    cB
    ccoss
    @0
    @7
    @11
    vx
    vy
    @0
    @6
    @10
    vu
    @0
    @3
    @8
    @5
    @9
    @1
    @2
    cA
    cB
    breq
    @1
    @4
    cA
    cB
    breq
    anbi12d
    exbidv
    opabbidv
    vx
    vy
    vu
    cA
    df-coss
    vx
    vy
    vu
    cB
    df-coss
    3eqtr4g
end
