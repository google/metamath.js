include "wo.mm"
include "wa.mm"
include "vneulem15.mm"
include "vneulem16.mm"
include "tr.mm"

theorem vneulem
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume vneulem.1: |- ( ( a v b ) ^ ( c v d ) ) = 0


  assert |- ( ( a v c ) ^ ( b v d ) ) = ( ( a ^ b ) v ( c ^ d ) )

  proof
    wva
    wvc
    wo
    #
    wvb
    wvd
    wo
    wa
    wva
    wvb
    wo
    #
    wvc
    wo
    @0
    wvd
    wo
    wa
    @1
    wvd
    wo
    wvb
    wvc
    wo
    wvd
    wo
    wa
    wa
    wva
    wvb
    wa
    wvc
    wvd
    wa
    wo
    wva
    wvb
    wvc
    wvd
    vneulem.1
    vneulem15
    wva
    wvb
    wvc
    wvd
    vneulem.1
    vneulem16
    tr
end
