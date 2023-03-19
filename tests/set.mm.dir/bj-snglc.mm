include "csn.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "bj-csngl.mm"
include "df-rex.mm"
include "bj-elsngl.mm"
include "elisset.mm"
include "pm4.71i.mm"
include "19.42v.mm"
include "wb.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "pm5.32ri.mm"
include "exbii.mm"
include "3bitr2i.mm"
include "cvv.mm"
include "vex.mm"
include "sneqbg.mm"
include "ax-mp.mm"
include "eqcom.mm"
include "bitr3i.mm"
include "anbi2i.mm"
include "bitri.mm"
include "3bitr4ri.mm"

theorem bj-snglc
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A e. B <-> { A } e. sngl B )

  proof
    cA
    csn
    #
    vx
    cv
    #
    csn
    #
    wceq
    #
    vx
    cB
    wrex
    @1
    cB
    wcel
    #
    @3
    wa
    #
    vx
    wex
    #
    @0
    cB
    bj-csngl
    wcel
    cA
    cB
    wcel
    #
    @3
    vx
    cB
    df-rex
    vx
    @0
    cB
    bj-elsngl
    @7
    @4
    @1
    cA
    wceq
    #
    wa
    #
    vx
    wex
    #
    @6
    @7
    @7
    @8
    vx
    wex
    #
    wa
    @7
    @8
    wa
    #
    vx
    wex
    @10
    @7
    @11
    vx
    cA
    cB
    elisset
    pm4.71i
    @7
    @8
    vx
    19.42v
    @12
    @9
    vx
    @8
    @7
    @4
    @7
    @4
    wb
    cA
    @1
    cA
    @1
    cB
    eleq1
    eqcoms
    pm5.32ri
    exbii
    3bitr2i
    @9
    @5
    vx
    @8
    @3
    @4
    @8
    @2
    @0
    wceq
    #
    @3
    @1
    cvv
    wcel
    @13
    @8
    wb
    vx
    vex
    @1
    cA
    cvv
    sneqbg
    ax-mp
    @2
    @0
    eqcom
    bitr3i
    anbi2i
    exbii
    bitri
    3bitr4ri
end
