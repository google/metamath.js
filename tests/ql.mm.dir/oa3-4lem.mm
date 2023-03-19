include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wt.mm"
include "tb.mm"
include "wi1.mm"
include "dfb.mm"
include "ax-a2.mm"
include "df-i1.mm"
include "an1.mm"
include "lor.mm"
include "3tr1.mm"
include "2an.mm"
include "2or.mm"
include "ax-r1.mm"
include "lan.mm"

theorem oa3-4lem
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( a ' ^ ( a v ( b ^ ( ( ( a ^ b ) v ( a ' ^ b ' ) ) v ( ( ( a ^ c ) v ( a ' ^ 1 ) ) ^ ( ( b ^ c ) v ( b ' ^ 1 ) ) ) ) ) ) ) = ( a ' ^ ( a v ( b ^ ( ( a == b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) )

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
    wvc
    wa
    #
    @0
    wt
    wa
    #
    wo
    #
    wvb
    wvc
    wa
    #
    @1
    wt
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
    @16
    @10
    @12
    @2
    @15
    @9
    wva
    wvb
    dfb
    @13
    @5
    @14
    @8
    @0
    @3
    wo
    @3
    @0
    wo
    @13
    @5
    @0
    @3
    ax-a2
    wva
    wvc
    df-i1
    @4
    @0
    @3
    @0
    an1
    lor
    3tr1
    @1
    @6
    wo
    @6
    @1
    wo
    @14
    @8
    @1
    @6
    ax-a2
    wvb
    wvc
    df-i1
    @7
    @1
    @6
    @1
    an1
    lor
    3tr1
    2an
    2or
    ax-r1
    lan
    lor
    lan
end
