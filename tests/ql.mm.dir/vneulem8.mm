include "wo.mm"
include "wa.mm"
include "vneulem6.mm"
include "vneulem7.mm"
include "tr.mm"

theorem vneulem8
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume vneulem6.1: |- ( ( a v b ) ^ ( c v d ) ) = 0


  assert |- ( ( ( a v b ) v d ) ^ ( ( b v c ) v d ) ) = ( b v d )

  proof
    wva
    wvb
    wo
    wvd
    wo
    wvb
    wvc
    wo
    wvd
    wo
    wa
    wvc
    wva
    wa
    wvb
    wvd
    wo
    #
    wo
    @0
    wva
    wvb
    wvc
    wvd
    vneulem6.1
    vneulem6
    wva
    wvb
    wvc
    wvd
    vneulem6.1
    vneulem7
    tr
end
