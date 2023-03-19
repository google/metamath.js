include "wo.mm"
include "i3le.mm"
include "le2or.mm"
include "oridm.mm"
include "lbtr.mm"
include "lei3.mm"

theorem binr3
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume binr3.1: |- ( a ->3 c ) = 1
  assume binr3.2: |- ( b ->3 c ) = 1


  assert |- ( ( a v b ) ->3 c ) = 1

  proof
    wva
    wvb
    wo
    #
    wvc
    @0
    wvc
    wvc
    wo
    wvc
    wva
    wvc
    wvb
    wvc
    wva
    wvc
    binr3.1
    i3le
    wvb
    wvc
    binr3.2
    i3le
    le2or
    wvc
    oridm
    lbtr
    lei3
end
