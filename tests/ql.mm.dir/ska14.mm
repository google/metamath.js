include "wn.mm"
include "wo.mm"
include "wi3.mm"
include "wt.mm"
include "lem4.mm"
include "ax-r1.mm"
include "ri3.mm"
include "i3id.mm"
include "ax-r2.mm"

theorem ska14
  let wva: term a
  let wvb: term b


  assert |- ( ( a ' v b ) ->3 ( a ->3 ( a ->3 b ) ) ) = 1

  proof
    wva
    wn
    wvb
    wo
    #
    wva
    wva
    wvb
    wi3
    wi3
    #
    wi3
    @1
    @1
    wi3
    wt
    @0
    @1
    @1
    @1
    @0
    wva
    wvb
    lem4
    ax-r1
    ri3
    @1
    i3id
    ax-r2
end
