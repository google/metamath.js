include "cin.mm"
include "cv.mm"
include "wf.mm"
include "cab.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "crab.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "df-f.mm"
include "baibr.mm"
include "syl.mm"
include "pm5.32i.mm"
include "elmap.mm"
include "anbi1i.mm"
include "fin.mm"
include "3bitr4ri.mm"
include "abbii.mm"
include "inex1.mm"
include "mapval.mm"
include "df-rab.mm"
include "3eqtr4i.mm"

theorem maprnin
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  assume maprnin.1: |- A e. _V
  assume maprnin.2: |- B e. _V

  disjoint A f
  disjoint B f
  disjoint C f
  assert |- ( ( B i^i C ) ^m A ) = { f e. ( B ^m A ) | ran f C_ C }

  proof
    cA
    cB
    cC
    cin
    #
    vf
    cv
    #
    wf
    #
    vf
    cab
    @1
    cB
    cA
    cmap
    co
    #
    wcel
    #
    @1
    crn
    cC
    wss
    #
    wa
    #
    vf
    cab
    @0
    cA
    cmap
    co
    @5
    vf
    @3
    crab
    @2
    @6
    vf
    cA
    cB
    @1
    wf
    #
    @5
    wa
    @7
    cA
    cC
    @1
    wf
    #
    wa
    @6
    @2
    @7
    @5
    @8
    @7
    @1
    cA
    wfn
    #
    @5
    @8
    wb
    cA
    cB
    @1
    ffn
    @8
    @9
    @5
    cA
    cC
    @1
    df-f
    baibr
    syl
    pm5.32i
    @4
    @7
    @5
    cB
    cA
    @1
    maprnin.2
    maprnin.1
    elmap
    anbi1i
    cA
    cB
    cC
    @1
    fin
    3bitr4ri
    abbii
    @0
    cA
    vf
    cB
    cC
    maprnin.2
    inex1
    maprnin.1
    mapval
    @5
    vf
    @3
    df-rab
    3eqtr4i
end
