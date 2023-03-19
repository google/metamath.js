include "wo.mm"
include "wa.mm"
include "vneulem10.mm"
include "vneulem8.mm"
include "2an.mm"
include "cm.mm"

theorem vneulem15
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume vneulem13.1: |- ( ( a v b ) ^ ( c v d ) ) = 0


  assert |- ( ( a v c ) ^ ( b v d ) ) = ( ( ( ( a v b ) v c ) ^ ( ( a v c ) v d ) ) ^ ( ( ( a v b ) v d ) ^ ( ( b v c ) v d ) ) )

  proof
    wva
    wvb
    wo
    #
    wvc
    wo
    wva
    wvc
    wo
    #
    wvd
    wo
    wa
    #
    @0
    wvd
    wo
    wvb
    wvc
    wo
    wvd
    wo
    wa
    #
    wa
    @1
    wvb
    wvd
    wo
    #
    wa
    @2
    @1
    @3
    @4
    wva
    wvb
    wvc
    wvd
    vneulem13.1
    vneulem10
    wva
    wvb
    wvc
    wvd
    vneulem13.1
    vneulem8
    2an
    cm
end
