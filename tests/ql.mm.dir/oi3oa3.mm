include "wi1.mm"
include "wa.mm"
include "wo.mm"
include "wt.mm"
include "oi3oa3lem1.mm"
include "lan.mm"
include "an1.mm"
include "ax-r2.mm"
include "ud1lem0b.mm"
include "2an.mm"
include "lor.mm"
include "ax-a2.mm"
include "r3a.mm"
include "1bi.mm"
include "3tr.mm"

theorem oi3oa3
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume oi3oa3.1: |- 1 = ( b == a )


  assert |- ( ( ( a ->1 c ) ^ ( b ->1 c ) ) v ( ( ( ( a ->1 c ) ^ ( ( ( a ->1 c ) ^ ( b ->1 c ) ) v ( a ^ b ) ) ) ->1 c ) ^ ( ( ( b ->1 c ) ^ ( ( ( a ->1 c ) ^ ( b ->1 c ) ) v ( a ^ b ) ) ) ->1 c ) ) ) = 1

  proof
    wva
    wvc
    wi1
    #
    wvb
    wvc
    wi1
    #
    wa
    #
    @0
    @2
    wva
    wvb
    wa
    wo
    #
    wa
    #
    wvc
    wi1
    #
    @1
    @3
    wa
    #
    wvc
    wi1
    #
    wa
    #
    wo
    @2
    @0
    wvc
    wi1
    #
    @1
    wvc
    wi1
    #
    wa
    #
    wo
    @11
    @2
    wo
    wt
    @8
    @11
    @2
    @5
    @9
    @7
    @10
    @4
    @0
    wvc
    @4
    @0
    wt
    wa
    @0
    @3
    wt
    @0
    wva
    wvb
    wvc
    oi3oa3.1
    oi3oa3lem1
    #
    lan
    @0
    an1
    ax-r2
    ud1lem0b
    @6
    @1
    wvc
    @6
    @1
    wt
    wa
    @1
    @3
    wt
    @1
    @12
    lan
    @1
    an1
    ax-r2
    ud1lem0b
    2an
    lor
    @2
    @11
    ax-a2
    @0
    @1
    wvc
    @1
    @0
    wvb
    wva
    wvc
    wvb
    wva
    oi3oa3.1
    r3a
    ud1lem0b
    1bi
    oi3oa3lem1
    3tr
end
