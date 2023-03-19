include "cv.mm"
include "csn.mm"
include "csb.mm"
include "wcel.mm"
include "wsbc.mm"
include "cab.mm"
include "wceq.mm"
include "abid.mm"
include "df-sbc.mm"
include "wa.mm"
include "wex.mm"
include "weq.mm"
include "clelab.mm"
include "velsn.mm"
include "anbi2i.mm"
include "exbii.mm"
include "eqeq2.mm"
include "pm5.32i.mm"
include "19.41v.mm"
include "simpr.mm"
include "cvv.mm"
include "eqvisset.mm"
include "elisset.mm"
include "syl.mm"
include "ancri.mm"
include "impbii.mm"
include "3bitri.mm"
include "df-csb.mm"
include "eleq2i.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem bj-csbsnlem
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- [_ A / x ]_ { x } = { A }

  proof
    vy
    vx
    cA
    vx
    cv
    #
    csn
    #
    csb
    #
    cA
    csn
    #
    vy
    cv
    #
    @4
    @1
    wcel
    #
    vx
    cA
    wsbc
    #
    vy
    cab
    #
    wcel
    #
    @4
    cA
    wceq
    #
    @4
    @2
    wcel
    @4
    @3
    wcel
    @8
    @6
    cA
    @5
    vx
    cab
    wcel
    #
    @9
    @6
    vy
    abid
    @5
    vx
    cA
    df-sbc
    @10
    @0
    cA
    wceq
    #
    @5
    wa
    #
    vx
    wex
    @11
    vy
    vx
    weq
    #
    wa
    #
    vx
    wex
    #
    @9
    @5
    vx
    cA
    clelab
    @12
    @14
    vx
    @5
    @13
    @11
    vy
    @0
    velsn
    anbi2i
    exbii
    @15
    @11
    @9
    wa
    #
    vx
    wex
    @11
    vx
    wex
    #
    @9
    wa
    #
    @9
    @14
    @16
    vx
    @11
    @13
    @9
    @0
    cA
    @4
    eqeq2
    pm5.32i
    exbii
    @11
    @9
    vx
    19.41v
    @18
    @9
    @17
    @9
    simpr
    @9
    @17
    @9
    cA
    cvv
    wcel
    @17
    vy
    cA
    eqvisset
    vx
    cA
    cvv
    elisset
    syl
    ancri
    impbii
    3bitri
    3bitri
    3bitri
    @2
    @7
    @4
    vx
    vy
    cA
    @1
    df-csb
    eleq2i
    vy
    cA
    velsn
    3bitr4i
    eqriv
end
