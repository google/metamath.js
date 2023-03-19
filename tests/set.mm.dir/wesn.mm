include "wrel.mm"
include "csn.mm"
include "wfr.mm"
include "wor.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wwe.mm"
include "frsn.mm"
include "sosn.mm"
include "anbi12d.mm"
include "df-we.mm"
include "pm4.24.mm"
include "3bitr4g.mm"

theorem wesn
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( Rel R -> ( R We { A } <-> -. A R A ) )

  proof
    cR
    wrel
    #
    cA
    csn
    #
    cR
    wfr
    #
    @1
    cR
    wor
    #
    wa
    cA
    cA
    cR
    wbr
    wn
    #
    @4
    wa
    @1
    cR
    wwe
    @4
    @0
    @2
    @4
    @3
    @4
    cA
    cR
    frsn
    cA
    cR
    sosn
    anbi12d
    @1
    cR
    df-we
    @4
    pm4.24
    3bitr4g
end
