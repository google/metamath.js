include "wn.mm"
include "wi3.mm"
include "wt.mm"
include "u3lem14a.mm"
include "ud3lem0a.mm"
include "i3th1.mm"
include "ax-r2.mm"

theorem u3lem14aa
  param wva: term a
  param wvb: term b


  assert |- ( a ->3 ( a ->3 ( ( b ->3 a ' ) ->3 b ' ) ) ) = 1

  proof
    wva
    wva
    wvb
    wva
    wn
    wi3
    wvb
    wn
    wi3
    wi3
    #
    wi3
    wva
    wva
    wvb
    wva
    wi3
    wi3
    #
    wi3
    wt
    @0
    @1
    wva
    wva
    wvb
    u3lem14a
    ud3lem0a
    wva
    wvb
    i3th1
    ax-r2
end
