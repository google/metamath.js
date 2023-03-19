include "wi3.mm"
include "wn.mm"
include "wo.mm"
include "leo.mm"
include "lem4.mm"
include "ax-r1.mm"
include "i3abs3.mm"
include "ax-r2.mm"
include "lbtr.mm"
include "lei3.mm"

theorem i3th8
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->3 b ) ' ->3 ( ( a ->3 b ) ->3 a ) ) = 1

  proof
    wva
    wvb
    wi3
    #
    wn
    #
    @0
    wva
    wi3
    #
    @1
    @1
    wva
    wo
    #
    @2
    @1
    wva
    leo
    @3
    @0
    @2
    wi3
    #
    @2
    @4
    @3
    @0
    wva
    lem4
    ax-r1
    wva
    wvb
    i3abs3
    ax-r2
    lbtr
    lei3
end
