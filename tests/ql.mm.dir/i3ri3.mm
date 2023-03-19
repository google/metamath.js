include "wi3.mm"
include "i3le.mm"
include "lebi.mm"
include "ri3.mm"
include "bile.mm"
include "lei3.mm"

theorem i3ri3
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume i3ri3.1: |- ( a ->3 b ) = 1
  assume i3ri3.2: |- ( b ->3 a ) = 1


  assert |- ( ( a ->3 c ) ->3 ( b ->3 c ) ) = 1

  proof
    wva
    wvc
    wi3
    #
    wvb
    wvc
    wi3
    #
    @0
    @1
    wva
    wvb
    wvc
    wva
    wvb
    wva
    wvb
    i3ri3.1
    i3le
    wvb
    wva
    i3ri3.2
    i3le
    lebi
    ri3
    bile
    lei3
end
