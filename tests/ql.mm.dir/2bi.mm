include "tb.mm"
include "lbi.mm"
include "rbi.mm"
include "ax-r2.mm"

theorem 2bi
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  assume 2bi.1: |- a = b
  assume 2bi.2: |- c = d


  assert |- ( a == c ) = ( b == d )

  proof
    wva
    wvc
    tb
    wva
    wvd
    tb
    wvb
    wvd
    tb
    wvc
    wvd
    wva
    2bi.2
    lbi
    wva
    wvb
    wvd
    2bi.1
    rbi
    ax-r2
end
