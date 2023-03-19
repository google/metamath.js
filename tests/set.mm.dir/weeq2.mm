include "wceq.mm"
include "wfr.mm"
include "wor.mm"
include "wa.mm"
include "wwe.mm"
include "freq2.mm"
include "soeq2.mm"
include "anbi12d.mm"
include "df-we.mm"
include "3bitr4g.mm"

theorem weeq2
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( A = B -> ( R We A <-> R We B ) )

  proof
    cA
    cB
    wceq
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
    cR
    wfr
    #
    cB
    cR
    wor
    #
    wa
    cA
    cR
    wwe
    cB
    cR
    wwe
    @0
    @1
    @3
    @2
    @4
    cA
    cB
    cR
    freq2
    cA
    cB
    cR
    soeq2
    anbi12d
    cA
    cR
    df-we
    cB
    cR
    df-we
    3bitr4g
end
