include "wo.mm"
include "leo.mm"
include "ax-a2.mm"
include "lbtr.mm"
include "lei3.mm"

theorem bina4
  let wva: term a
  let wvb: term b


  assert |- ( b ->3 ( a v b ) ) = 1

  proof
    wvb
    wva
    wvb
    wo
    #
    wvb
    wvb
    wva
    wo
    @0
    wvb
    wva
    leo
    wvb
    wva
    ax-a2
    lbtr
    lei3
end
