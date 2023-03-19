include "wi3.mm"
include "wn.mm"
include "wo.mm"
include "wt.mm"
include "lem4.mm"
include "ax-r2.mm"

theorem i0i3
  param wva: term a
  param wvb: term b
  assume i0i3.1: |- ( a ' v b ) = 1


  assert |- ( a ->3 ( a ->3 b ) ) = 1

  proof
    wva
    wva
    wvb
    wi3
    wi3
    wva
    wn
    wvb
    wo
    wt
    wva
    wvb
    lem4
    i0i3.1
    ax-r2
end
