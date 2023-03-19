include "tb.mm"
include "wt.mm"
include "bicom.mm"
include "ax-r2.mm"

theorem wr1
  let wva: term a
  let wvb: term b
  assume wr1.1: |- ( a == b ) = 1


  assert |- ( b == a ) = 1

  proof
    wvb
    wva
    tb
    wva
    wvb
    tb
    wt
    wvb
    wva
    bicom
    wr1.1
    ax-r2
end
