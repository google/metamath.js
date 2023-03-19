include "wo.mm"
include "i3orcom.mm"
include "i3ror.mm"
include "binr2.mm"

theorem i3lor
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume i3lor.1: |- ( a ->3 b ) = 1


  assert |- ( ( c v a ) ->3 ( c v b ) ) = 1

  proof
    wvc
    wva
    wo
    wva
    wvc
    wo
    #
    wvc
    wvb
    wo
    #
    wvc
    wva
    i3orcom
    @0
    wvb
    wvc
    wo
    @1
    wva
    wvb
    wvc
    i3lor.1
    i3ror
    wvb
    wvc
    i3orcom
    binr2
    binr2
end
