include "c0.mm"
include "wne.mm"
include "wtr.mm"
include "wa.mm"
include "cint.mm"
include "cv.mm"
include "wcel.mm"
include "wel.mm"
include "wral.mm"
include "vex.mm"
include "elint2.mm"
include "wrex.mm"
include "r19.2z.mm"
include "ex.mm"
include "trel.mm"
include "expcomd.mm"
include "rexlimdv.mm"
include "sylan9.mm"
include "syl5bi.mm"
include "ssrdv.mm"

theorem trintssOLD
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( ( A =/= (/) /\ Tr A ) -> |^| A C_ A )

  proof
    cA
    c0
    wne
    #
    cA
    wtr
    #
    wa
    #
    vy
    cA
    cint
    #
    cA
    vy
    cv
    #
    @3
    wcel
    vy
    vx
    wel
    #
    vx
    cA
    wral
    #
    @2
    @4
    cA
    wcel
    #
    vx
    @4
    cA
    vy
    vex
    elint2
    @0
    @6
    @5
    vx
    cA
    wrex
    #
    @1
    @7
    @0
    @6
    @8
    @5
    vx
    cA
    r19.2z
    ex
    @1
    @5
    @7
    vx
    cA
    @1
    @5
    vx
    cv
    #
    cA
    wcel
    @7
    cA
    @4
    @9
    trel
    expcomd
    rexlimdv
    sylan9
    syl5bi
    ssrdv
end
