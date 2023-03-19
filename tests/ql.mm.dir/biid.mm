include "wa.mm"
include "wn.mm"
include "wo.mm"
include "tb.mm"
include "wt.mm"
include "anidm.mm"
include "2or.mm"
include "dfb.mm"
include "df-t.mm"
include "3tr1.mm"

theorem biid
  param wva: term a


  assert |- ( a == a ) = 1

  proof
    wva
    wva
    wa
    #
    wva
    wn
    #
    @1
    wa
    #
    wo
    wva
    @1
    wo
    wva
    wva
    tb
    wt
    @0
    wva
    @2
    @1
    wva
    anidm
    @1
    anidm
    2or
    wva
    wva
    dfb
    wva
    df-t
    3tr1
end
