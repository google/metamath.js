include "con0.mm"
include "wcel.mm"
include "cv.mm"
include "crab.mm"
include "cint.mm"
include "csuc.mm"
include "wss.mm"
include "word.mm"
include "wb.mm"
include "eloni.mm"
include "ordelsuc.mm"
include "sylan2.mm"
include "rabbidva.mm"
include "inteqd.mm"
include "wceq.mm"
include "sucelon.mm"
include "intmin.mm"
include "sylbi.mm"
include "eqtr2d.mm"

theorem onsucmin
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. On -> suc A = |^| { x e. On | A e. x } )

  proof
    cA
    con0
    wcel
    #
    cA
    vx
    cv
    #
    wcel
    #
    vx
    con0
    crab
    #
    cint
    cA
    csuc
    #
    @1
    wss
    #
    vx
    con0
    crab
    #
    cint
    #
    @4
    @0
    @3
    @6
    @0
    @2
    @5
    vx
    con0
    @1
    con0
    wcel
    @0
    @1
    word
    @2
    @5
    wb
    @1
    eloni
    cA
    @1
    con0
    ordelsuc
    sylan2
    rabbidva
    inteqd
    @0
    @4
    con0
    wcel
    @7
    @4
    wceq
    cA
    sucelon
    vx
    @4
    con0
    intmin
    sylbi
    eqtr2d
end
