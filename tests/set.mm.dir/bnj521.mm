include "csn.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wn.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "elirr.mm"
include "wa.mm"
include "elin.mm"
include "velsn.mm"
include "eleq1.mm"
include "biimpac.mm"
include "sylan2b.mm"
include "sylbi.mm"
include "exlimiv.mm"
include "mto.mm"
include "n0.mm"
include "mtbir.mm"
include "nne.mm"
include "mpbi.mm"

theorem bnj521
  let cA: class A
  let vx: setvar x


  assert |- ( A i^i { A } ) = (/)

  proof
    cA
    cA
    csn
    #
    cin
    #
    c0
    wne
    #
    wn
    @1
    c0
    wceq
    @2
    vx
    cv
    #
    @1
    wcel
    #
    vx
    wex
    #
    @5
    cA
    cA
    wcel
    #
    cA
    elirr
    @4
    @6
    vx
    @4
    @3
    cA
    wcel
    #
    @3
    @0
    wcel
    #
    wa
    @6
    @3
    cA
    @0
    elin
    @8
    @7
    @3
    cA
    wceq
    #
    @6
    vx
    cA
    velsn
    @9
    @7
    @6
    @3
    cA
    cA
    eleq1
    biimpac
    sylan2b
    sylbi
    exlimiv
    mto
    vx
    @1
    n0
    mtbir
    @1
    c0
    nne
    mpbi
end
