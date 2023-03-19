include "wiso.mm"
include "wfr.mm"
include "wor.mm"
include "wa.mm"
include "wwe.mm"
include "isofr.mm"
include "isoso.mm"
include "anbi12d.mm"
include "df-we.mm"
include "3bitr4g.mm"

theorem isowe
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let vx: setvar x
  let vy: setvar y


  assert |- ( H Isom R , S ( A , B ) -> ( R We A <-> S We B ) )

  proof
    cA
    cB
    cR
    cS
    cH
    wiso
    #
    cA
    cR
    wfr
    #
    cA
    cR
    wor
    #
    wa
    cB
    cS
    wfr
    #
    cB
    cS
    wor
    #
    wa
    cA
    cR
    wwe
    cB
    cS
    wwe
    @0
    @1
    @3
    @2
    @4
    cA
    cB
    cR
    cS
    cH
    isofr
    cA
    cB
    cR
    cS
    cH
    isoso
    anbi12d
    cA
    cR
    df-we
    cB
    cS
    df-we
    3bitr4g
end
