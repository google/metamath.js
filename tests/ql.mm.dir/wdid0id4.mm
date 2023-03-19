include "wid4.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "wt.mm"
include "df-id4.mm"
include "wid0.mm"
include "df-id0.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "wddi3.mm"
include "wa2.mm"
include "wlan.mm"
include "wa4.mm"
include "wleoa.mm"
include "wr2.mm"
include "wr1.mm"
include "wwbmp.mm"

theorem wdid0id4
  let wva: term a
  let wvb: term b
  assume wdid0id5.1: |- ( a ==0 b ) = 1


  assert |- ( a ==4 b ) = 1

  proof
    wva
    wvb
    wid4
    wva
    wn
    wvb
    wo
    #
    wvb
    wn
    #
    wva
    wvb
    wa
    wo
    #
    wa
    #
    wt
    wva
    wvb
    df-id4
    @0
    @1
    wva
    wo
    #
    wa
    #
    @3
    @5
    wva
    wvb
    wid0
    #
    wt
    @6
    @5
    wva
    wvb
    df-id0
    ax-r1
    wdid0id5.1
    ax-r2
    @4
    @2
    @0
    @2
    @4
    @2
    @4
    @1
    wvb
    wo
    #
    wa
    #
    @4
    @1
    wva
    wvb
    wddi3
    @8
    @4
    wvb
    @1
    wo
    #
    wa
    @4
    @7
    @9
    @4
    @1
    wvb
    wa2
    wlan
    @4
    @9
    @9
    @4
    wvb
    wa4
    wleoa
    wr2
    wr2
    wr1
    wlan
    wwbmp
    ax-r2
end
