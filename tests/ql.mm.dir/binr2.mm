include "i3le.mm"
include "letr.mm"
include "lei3.mm"

theorem binr2
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume binr2.1: |- ( a ->3 b ) = 1
  assume binr2.2: |- ( b ->3 c ) = 1


  assert |- ( a ->3 c ) = 1

  proof
    wva
    wvc
    wva
    wvb
    wvc
    wva
    wvb
    binr2.1
    i3le
    wvb
    wvc
    binr2.2
    i3le
    letr
    lei3
end
