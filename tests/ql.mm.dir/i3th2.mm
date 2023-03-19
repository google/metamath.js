include "wi3.mm"
include "wn.mm"
include "wo.mm"
include "wt.mm"
include "lem4.mm"
include "li3.mm"
include "bina4.mm"
include "ax-r2.mm"

theorem i3th2
  let wva: term a
  let wvb: term b


  assert |- ( a ->3 ( b ->3 ( b ->3 a ) ) ) = 1

  proof
    wva
    wvb
    wvb
    wva
    wi3
    wi3
    #
    wi3
    wva
    wvb
    wn
    #
    wva
    wo
    #
    wi3
    wt
    @0
    @2
    wva
    wvb
    wva
    lem4
    li3
    @1
    wva
    bina4
    ax-r2
end
