include "wcmtr.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wt.mm"
include "df-cmtr.mm"
include "or42.mm"
include "tb.mm"
include "dfb.mm"
include "ax-a1.mm"
include "lan.mm"
include "ax-r1.mm"
include "lor.mm"
include "ax-r2.mm"
include "2or.mm"
include "ax-wdol.mm"
include "3tr.mm"

theorem wdcom
  let wva: term a
  let wvb: term b


  assert |- C ( a , b ) = 1

  proof
    wva
    wvb
    wcmtr
    wva
    wvb
    wa
    #
    wva
    wvb
    wn
    #
    wa
    #
    wo
    wva
    wn
    #
    wvb
    wa
    #
    @3
    @1
    wa
    #
    wo
    wo
    @0
    @5
    wo
    #
    @2
    @4
    wo
    #
    wo
    #
    wt
    wva
    wvb
    df-cmtr
    @0
    @2
    @4
    @5
    or42
    @8
    wva
    wvb
    tb
    #
    wva
    @1
    tb
    #
    wo
    #
    wt
    @11
    @8
    @9
    @6
    @10
    @7
    wva
    wvb
    dfb
    @10
    @2
    @3
    @1
    wn
    #
    wa
    #
    wo
    @7
    wva
    @1
    dfb
    @13
    @4
    @2
    @4
    @13
    wvb
    @12
    @3
    wvb
    ax-a1
    lan
    ax-r1
    lor
    ax-r2
    2or
    ax-r1
    wva
    wvb
    ax-wdol
    ax-r2
    3tr
end
