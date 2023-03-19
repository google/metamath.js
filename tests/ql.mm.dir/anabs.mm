include "wo.mm"
include "wa.mm"
include "wn.mm"
include "ax-a1.mm"
include "ax-r5.mm"
include "lan.mm"
include "df-a.mm"
include "ax-r2.mm"
include "ax-a5.mm"
include "con2.mm"

theorem anabs
  param wva: term a
  param wvb: term b


  assert |- ( a ^ ( a v b ) ) = a

  proof
    wva
    wva
    wvb
    wo
    #
    wa
    #
    wva
    wn
    #
    @2
    wn
    #
    wvb
    wo
    #
    wn
    wo
    #
    wn
    #
    wva
    @1
    wva
    @4
    wa
    @6
    @0
    @4
    wva
    wva
    @3
    wvb
    wva
    ax-a1
    ax-r5
    lan
    wva
    @4
    df-a
    ax-r2
    @5
    wva
    @2
    wvb
    ax-a5
    con2
    ax-r2
end
