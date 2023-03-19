include "wi3.mm"
include "li3.mm"
include "ri3.mm"
include "ax-r2.mm"

theorem 2i3
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume 2i3.1: |- a = b
  assume 2i3.2: |- c = d


  assert |- ( a ->3 c ) = ( b ->3 d )

  proof
    wva
    wvc
    wi3
    wva
    wvd
    wi3
    wvb
    wvd
    wi3
    wvc
    wvd
    wva
    2i3.2
    li3
    wva
    wvb
    wvd
    2i3.1
    ri3
    ax-r2
end
