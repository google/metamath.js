include "wn.mm"
include "wo.mm"
include "i3i0.mm"
include "i3lor.mm"
include "skmp3.mm"
include "i0i3.mm"

theorem i0i3tr
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume i0i3tr.1: |- ( a ->3 ( a ->3 b ) ) = 1
  assume i0i3tr.2: |- ( b ->3 c ) = 1


  assert |- ( a ->3 ( a ->3 c ) ) = 1

  proof
    wva
    wvc
    wva
    wn
    #
    wvb
    wo
    @0
    wvc
    wo
    wva
    wvb
    i0i3tr.1
    i3i0
    wvb
    wvc
    @0
    i0i3tr.2
    i3lor
    skmp3
    i0i3
end
