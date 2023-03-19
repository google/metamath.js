include "ax-r1.mm"
include "i33tr1.mm"

theorem i33tr2
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  assume i33tr2.1: |- ( a ->3 b ) = 1
  assume i33tr2.2: |- a = c
  assume i33tr2.3: |- b = d


  assert |- ( c ->3 d ) = 1

  proof
    wva
    wvb
    wvc
    wvd
    i33tr2.1
    wva
    wvc
    i33tr2.2
    ax-r1
    wvb
    wvd
    i33tr2.3
    ax-r1
    i33tr1
end
