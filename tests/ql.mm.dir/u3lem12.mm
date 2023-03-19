include "wn.mm"
include "wi3.mm"
include "wo.mm"
include "wa.mm"
include "lem4.mm"
include "ax-r4.mm"
include "df-a.mm"
include "ax-r1.mm"
include "ax-r2.mm"

theorem u3lem12
  param wva: term a
  param wvb: term b


  assert |- ( a ->3 ( a ->3 b ' ) ) ' = ( a ^ b )

  proof
    wva
    wva
    wvb
    wn
    #
    wi3
    wi3
    #
    wn
    wva
    wn
    @0
    wo
    #
    wn
    #
    wva
    wvb
    wa
    #
    @1
    @2
    wva
    @0
    lem4
    ax-r4
    @4
    @3
    wva
    wvb
    df-a
    ax-r1
    ax-r2
end
