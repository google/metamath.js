include "con0.mm"
include "wss.mm"
include "word.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "csuc.mm"
include "wcel.mm"
include "cuni.mm"
include "wb.mm"
include "ssel2.mm"
include "ordsssuc.mm"
include "sylan.mm"
include "an32s.mm"
include "ralbidva.mm"
include "unissb.mm"
include "dfss3.mm"
include "3bitr4g.mm"

theorem ordunisssuc
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A C_ On /\ Ord B ) -> ( U. A C_ B <-> A C_ suc B ) )

  proof
    cA
    con0
    wss
    #
    cB
    word
    #
    wa
    #
    vx
    cv
    #
    cB
    wss
    #
    vx
    cA
    wral
    @3
    cB
    csuc
    #
    wcel
    #
    vx
    cA
    wral
    cA
    cuni
    cB
    wss
    cA
    @5
    wss
    @2
    @4
    @6
    vx
    cA
    @0
    @3
    cA
    wcel
    #
    @1
    @4
    @6
    wb
    #
    @0
    @7
    wa
    @3
    con0
    wcel
    @1
    @8
    cA
    con0
    @3
    ssel2
    @3
    cB
    ordsssuc
    sylan
    an32s
    ralbidva
    vx
    cA
    cB
    unissb
    vx
    cA
    @5
    dfss3
    3bitr4g
end
