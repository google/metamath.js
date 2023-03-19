include "word.mm"
include "con0.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "csuc.mm"
include "cuni.mm"
include "ordeleqon.mm"
include "cv.mm"
include "suceq.mm"
include "unieqd.mm"
include "id.mm"
include "eqeq12d.mm"
include "wtr.mm"
include "eloni.mm"
include "ordtr.mm"
include "syl.mm"
include "vex.mm"
include "unisuc.mm"
include "sylib.mm"
include "vtoclga.mm"
include "sucon.mm"
include "unieqi.mm"
include "unon.mm"
include "eqtri.mm"
include "3eqtr4a.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem ordunisuc
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( Ord A -> U. suc A = A )

  proof
    cA
    word
    cA
    con0
    wcel
    #
    cA
    con0
    wceq
    #
    wo
    cA
    csuc
    #
    cuni
    #
    cA
    wceq
    #
    cA
    ordeleqon
    @0
    @4
    @1
    vx
    cv
    #
    csuc
    #
    cuni
    #
    @5
    wceq
    #
    @4
    vx
    cA
    con0
    @5
    cA
    wceq
    #
    @7
    @3
    @5
    cA
    @9
    @6
    @2
    @5
    cA
    suceq
    unieqd
    @9
    id
    eqeq12d
    @5
    con0
    wcel
    #
    @5
    wtr
    #
    @8
    @10
    @5
    word
    @11
    @5
    eloni
    @5
    ordtr
    syl
    @5
    vx
    vex
    unisuc
    sylib
    vtoclga
    @1
    con0
    csuc
    #
    cuni
    #
    con0
    @3
    cA
    @13
    con0
    cuni
    con0
    @12
    con0
    sucon
    unieqi
    unon
    eqtri
    @1
    @2
    @12
    cA
    con0
    suceq
    unieqd
    @1
    id
    3eqtr4a
    jaoi
    sylbi
end
