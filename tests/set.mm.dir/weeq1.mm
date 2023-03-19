include "wceq.mm"
include "wfr.mm"
include "wor.mm"
include "wa.mm"
include "wwe.mm"
include "freq1.mm"
include "soeq1.mm"
include "anbi12d.mm"
include "df-we.mm"
include "3bitr4g.mm"

theorem weeq1
  let cA: class A
  let cR: class R
  let cS: class S


  assert |- ( R = S -> ( R We A <-> S We A ) )

  proof
    cR
    cS
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
    cA
    cS
    wfr
    #
    cA
    cS
    wor
    #
    wa
    cA
    cR
    wwe
    cA
    cS
    wwe
    @0
    @1
    @3
    @2
    @4
    cA
    cR
    cS
    freq1
    cA
    cR
    cS
    soeq1
    anbi12d
    cA
    cR
    df-we
    cA
    cS
    df-we
    3bitr4g
end
