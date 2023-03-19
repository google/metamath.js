include "word.mm"
include "cpw.mm"
include "con0.mm"
include "cin.mm"
include "csuc.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "elin.mm"
include "selpw.mm"
include "anbi2ci.mm"
include "bitri.mm"
include "wb.mm"
include "ordsssuc.mm"
include "expcom.mm"
include "pm5.32d.mm"
include "simpr.mm"
include "wi.mm"
include "ordsuc.mm"
include "ordelon.mm"
include "ex.mm"
include "sylbi.mm"
include "ancrd.mm"
include "impbid2.mm"
include "bitrd.mm"
include "syl5bb.mm"
include "eqrdv.mm"

theorem ordpwsuc
  let cA: class A
  let vx: setvar x


  assert |- ( Ord A -> ( ~P A i^i On ) = suc A )

  proof
    cA
    word
    #
    vx
    cA
    cpw
    #
    con0
    cin
    #
    cA
    csuc
    #
    vx
    cv
    #
    @2
    wcel
    #
    @4
    con0
    wcel
    #
    @4
    cA
    wss
    #
    wa
    #
    @0
    @4
    @3
    wcel
    #
    @5
    @4
    @1
    wcel
    #
    @6
    wa
    @8
    @4
    @1
    con0
    elin
    @10
    @7
    @6
    vx
    cA
    selpw
    anbi2ci
    bitri
    @0
    @8
    @6
    @9
    wa
    #
    @9
    @0
    @6
    @7
    @9
    @6
    @0
    @7
    @9
    wb
    @4
    cA
    ordsssuc
    expcom
    pm5.32d
    @0
    @11
    @9
    @6
    @9
    simpr
    @0
    @9
    @6
    @0
    @3
    word
    #
    @9
    @6
    wi
    cA
    ordsuc
    @12
    @9
    @6
    @3
    @4
    ordelon
    ex
    sylbi
    ancrd
    impbid2
    bitrd
    syl5bb
    eqrdv
end
