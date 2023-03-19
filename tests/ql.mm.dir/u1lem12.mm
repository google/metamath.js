include "wi1.mm"
include "wn.mm"
include "ax-a1.mm"
include "ud1lem0b.mm"
include "u1lem11.mm"
include "ax-r2.mm"

theorem u1lem12
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->1 b ) ->1 b ) = ( a ' ->1 b )

  proof
    wva
    wvb
    wi1
    #
    wvb
    wi1
    wva
    wn
    #
    wn
    #
    wvb
    wi1
    #
    wvb
    wi1
    @1
    wvb
    wi1
    @0
    @3
    wvb
    wva
    @2
    wvb
    wva
    ax-a1
    ud1lem0b
    ud1lem0b
    @1
    wvb
    u1lem11
    ax-r2
end
