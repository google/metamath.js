include "csn.mm"
include "cop.mm"
include "whe.mm"
include "cima.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "wceq.mm"
include "vex.mm"
include "elima3.mm"
include "velsn.mm"
include "imbi12i.mm"
include "albii.mm"
include "w3a.mm"
include "opex.mm"
include "elsn.mm"
include "opth.mm"
include "bitri.mm"
include "anbi12i.mm"
include "3anass.mm"
include "bitr4i.mm"
include "simp3.mm"
include "simp2.mm"
include "simp1.mm"
include "3eqtr2d.mm"
include "sylbi.mm"
include "exlimiv.mm"
include "mpgbir.mm"
include "dfss2.mm"
include "mpbir.mm"
include "df-he.mm"

theorem snhesn
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- { <. A , A >. } hereditary { B }

  proof
    cB
    csn
    #
    cA
    cA
    cop
    #
    csn
    #
    whe
    @2
    @0
    cima
    #
    @0
    wss
    #
    @4
    vx
    cv
    #
    @3
    wcel
    #
    @5
    @0
    wcel
    #
    wi
    #
    vx
    wal
    #
    @9
    vy
    cv
    #
    @0
    wcel
    #
    @10
    @5
    cop
    #
    @2
    wcel
    #
    wa
    #
    vy
    wex
    #
    @5
    cB
    wceq
    #
    wi
    #
    vx
    @8
    @17
    vx
    @6
    @15
    @7
    @16
    vy
    @5
    @2
    @0
    vx
    vex
    #
    elima3
    vx
    cB
    velsn
    imbi12i
    albii
    @14
    @16
    vy
    @14
    @10
    cB
    wceq
    #
    @10
    cA
    wceq
    #
    @5
    cA
    wceq
    #
    w3a
    #
    @16
    @14
    @19
    @20
    @21
    wa
    #
    wa
    @22
    @11
    @19
    @13
    @23
    vy
    cB
    velsn
    @13
    @12
    @1
    wceq
    @23
    @12
    @1
    @10
    @5
    opex
    elsn
    @10
    @5
    cA
    cA
    vy
    vex
    @18
    opth
    bitri
    anbi12i
    @19
    @20
    @21
    3anass
    bitr4i
    @22
    @5
    cA
    @10
    cB
    @19
    @20
    @21
    simp3
    @19
    @20
    @21
    simp2
    @19
    @20
    @21
    simp1
    3eqtr2d
    sylbi
    exlimiv
    mpgbir
    vx
    @3
    @0
    dfss2
    mpbir
    @0
    @2
    df-he
    mpbir
end
