include "tb.mm"
include "wt.mm"
include "bi1.mm"
include "ax-r1.mm"

theorem 1bi
  param wva: term a
  param wvb: term b
  assume 1bi.1: |- a = b


  assert |- 1 = ( a == b )

  proof
    wva
    wvb
    tb
    wt
    wva
    wvb
    1bi.1
    bi1
    ax-r1
end
