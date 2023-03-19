include "wo.mm"
include "wa.mm"
include "ax-a2.mm"
include "2an.mm"
include "ancom.mm"
include "lor.mm"
include "lan.mm"
include "le3tr1.mm"

theorem oa3to4lem5
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume oa3to4lem5.1: |- ( ( a v b ) ^ ( c v d ) ) =< ( a v ( b ^ ( d v ( ( a v c ) ^ ( b v d ) ) ) ) )


  assert |- ( ( b v a ) ^ ( d v c ) ) =< ( a v ( b ^ ( d v ( ( b v d ) ^ ( a v c ) ) ) ) )

  proof
    wva
    wvb
    wo
    #
    wvc
    wvd
    wo
    #
    wa
    wva
    wvb
    wvd
    wva
    wvc
    wo
    #
    wvb
    wvd
    wo
    #
    wa
    #
    wo
    #
    wa
    #
    wo
    wvb
    wva
    wo
    #
    wvd
    wvc
    wo
    #
    wa
    wva
    wvb
    wvd
    @3
    @2
    wa
    #
    wo
    #
    wa
    #
    wo
    oa3to4lem5.1
    @7
    @0
    @8
    @1
    wvb
    wva
    ax-a2
    wvd
    wvc
    ax-a2
    2an
    @11
    @6
    wva
    @10
    @5
    wvb
    @9
    @4
    wvd
    @3
    @2
    ancom
    lor
    lan
    lor
    le3tr1
end
