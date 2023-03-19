include "wi1.mm"
include "u1lem1.mm"
include "ax-r4.mm"

theorem u1lem1n
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->1 b ) ->1 a ) ' = a '

  proof
    wva
    wvb
    wi1
    wva
    wi1
    wva
    wva
    wvb
    u1lem1
    ax-r4
end
