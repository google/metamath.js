include "wi1.mm"
include "ud1lem0b.mm"
include "ud1lem0a.mm"
include "ax-r2.mm"

theorem ud1lem0ab
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  assume ud1lem0ab.1: |- a = b
  assume ud1lem0ab.2: |- c = d


  assert |- ( a ->1 c ) = ( b ->1 d )

  proof
    wva
    wvc
    wi1
    wvb
    wvc
    wi1
    wvb
    wvd
    wi1
    wva
    wvb
    wvc
    ud1lem0ab.1
    ud1lem0b
    wvc
    wvd
    wvb
    ud1lem0ab.2
    ud1lem0a
    ax-r2
end
