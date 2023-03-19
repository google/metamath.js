include "wfr.mm"
include "wor.mm"
include "wa.mm"
include "cxp.mm"
include "cin.mm"
include "wwe.mm"
include "frinxp.mm"
include "soinxp.mm"
include "anbi12i.mm"
include "df-we.mm"
include "3bitr4i.mm"

theorem weinxp
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R We A <-> ( R i^i ( A X. A ) ) We A )

  proof
    cA
    cR
    wfr
    #
    cA
    cR
    wor
    #
    wa
    cA
    cR
    cA
    cA
    cxp
    cin
    #
    wfr
    #
    cA
    @2
    wor
    #
    wa
    cA
    cR
    wwe
    cA
    @2
    wwe
    @0
    @3
    @1
    @4
    cA
    cR
    frinxp
    cA
    cR
    soinxp
    anbi12i
    cA
    cR
    df-we
    cA
    @2
    df-we
    3bitr4i
end
