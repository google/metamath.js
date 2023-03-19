include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wt.mm"
include "tb.mm"
include "wi1.mm"
include "dfb.mm"
include "ax-r1.mm"
include "an1.mm"
include "ax-a1.mm"
include "ax-r2.mm"
include "ax-r5.mm"
include "df-i1.mm"
include "2an.mm"
include "2or.mm"
include "lan.mm"
include "lor.mm"

theorem oa3-3lem
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( a ' ^ ( a v ( b ^ ( ( ( a ^ b ) v ( a ' ^ b ' ) ) v ( ( ( a ^ 1 ) v ( a ' ^ c ) ) ^ ( ( b ^ 1 ) v ( b ' ^ c ) ) ) ) ) ) ) = ( a ' ^ ( a v ( b ^ ( ( a == b ) v ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) ) ) ) )

  proof
    wva
    wvb
    wva
    wvb
    wa
    wva
    wn
    #
    wvb
    wn
    #
    wa
    wo
    #
    wva
    wt
    wa
    #
    @0
    wvc
    wa
    #
    wo
    #
    wvb
    wt
    wa
    #
    @1
    wvc
    wa
    #
    wo
    #
    wa
    #
    wo
    #
    wa
    #
    wo
    wva
    wvb
    wva
    wvb
    tb
    #
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
    #
    wa
    #
    wo
    @0
    @11
    @17
    wva
    @10
    @16
    wvb
    @2
    @12
    @9
    @15
    @12
    @2
    wva
    wvb
    dfb
    ax-r1
    @5
    @13
    @8
    @14
    @5
    @0
    wn
    #
    @4
    wo
    #
    @13
    @3
    @18
    @4
    @3
    wva
    @18
    wva
    an1
    wva
    ax-a1
    ax-r2
    ax-r5
    @13
    @19
    @0
    wvc
    df-i1
    ax-r1
    ax-r2
    @8
    @1
    wn
    #
    @7
    wo
    #
    @14
    @6
    @20
    @7
    @6
    wvb
    @20
    wvb
    an1
    wvb
    ax-a1
    ax-r2
    ax-r5
    @14
    @21
    @1
    wvc
    df-i1
    ax-r1
    ax-r2
    2an
    2or
    lan
    lor
    lan
end
