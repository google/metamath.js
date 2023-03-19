include "wo.mm"
include "wa.mm"
include "ancom.mm"
include "an4.mm"
include "vneulem9.mm"
include "vneulem11.mm"
include "2an.mm"
include "tr.mm"
include "vneulem14.mm"
include "orcom.mm"
include "3tr.mm"

theorem vneulem16
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume vneulem13.1: |- ( ( a v b ) ^ ( c v d ) ) = 0


  assert |- ( ( ( ( a v b ) v c ) ^ ( ( a v c ) v d ) ) ^ ( ( ( a v b ) v d ) ^ ( ( b v c ) v d ) ) ) = ( ( a ^ b ) v ( c ^ d ) )

  proof
    wva
    wvb
    wo
    #
    wvc
    wo
    #
    wva
    wvc
    wo
    wvd
    wo
    #
    wa
    #
    @0
    wvd
    wo
    #
    wvb
    wvc
    wo
    wvd
    wo
    #
    wa
    #
    wa
    @6
    @3
    wa
    #
    wvc
    wvd
    wa
    #
    @0
    wo
    #
    wvc
    wvd
    wo
    wva
    wvb
    wa
    #
    wo
    #
    wa
    #
    @10
    @8
    wo
    #
    @3
    @6
    ancom
    @7
    @4
    @1
    wa
    #
    @5
    @2
    wa
    #
    wa
    @12
    @4
    @5
    @1
    @2
    an4
    @14
    @9
    @15
    @11
    wva
    wvb
    wvc
    wvd
    vneulem13.1
    vneulem9
    wva
    wvb
    wvc
    wvd
    vneulem13.1
    vneulem11
    2an
    tr
    @12
    @8
    @10
    wo
    @13
    wva
    wvb
    wvc
    wvd
    vneulem13.1
    vneulem14
    @8
    @10
    orcom
    tr
    3tr
end
