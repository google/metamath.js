include "wo.mm"
include "wa.mm"
include "testmod.mm"
include "orcom.mm"
include "ancom.mm"
include "lor.mm"
include "tr.mm"
include "lan.mm"

theorem testmod1
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d


  assert |- ( ( ( c v a ) v ( ( b v c ) ^ ( d v a ) ) ) ^ ( a v ( b ^ ( d v ( ( a v c ) ^ ( b v d ) ) ) ) ) ) = ( a v ( b ^ ( ( ( a v c ) ^ ( b v d ) ) v ( d ^ ( ( a v c ) v ( ( b v c ) ^ ( d v a ) ) ) ) ) ) )

  proof
    wvc
    wva
    wo
    wvb
    wvc
    wo
    wvd
    wva
    wo
    wa
    #
    wo
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
    wa
    #
    wo
    wa
    wo
    wa
    wvb
    @1
    @0
    wo
    #
    wvd
    wa
    #
    @2
    wo
    #
    wa
    #
    wva
    wo
    #
    wva
    wvb
    @2
    wvd
    @3
    wa
    #
    wo
    #
    wa
    #
    wo
    #
    wva
    wvb
    wvc
    wvd
    testmod
    @7
    wva
    @6
    wo
    @11
    @6
    wva
    orcom
    @6
    @10
    wva
    @5
    @9
    wvb
    @5
    @2
    @4
    wo
    @9
    @4
    @2
    orcom
    @4
    @8
    @2
    @3
    wvd
    ancom
    lor
    tr
    lan
    lor
    tr
    tr
end
