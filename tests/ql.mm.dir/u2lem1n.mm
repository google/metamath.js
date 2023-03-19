include "wi2.mm"
include "u2lem1.mm"
include "ax-r4.mm"

theorem u2lem1n
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->2 b ) ->2 a ) ' = a '

  proof
    wva
    wvb
    wi2
    wva
    wi2
    wva
    wva
    wvb
    u2lem1
    ax-r4
end
