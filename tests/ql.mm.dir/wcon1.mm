include "tb.mm"
include "wn.mm"
include "wt.mm"
include "conb.mm"
include "ax-r2.mm"

theorem wcon1
  param wva: term a
  param wvb: term b
  assume wcon1.1: |- ( a ' == b ' ) = 1


  assert |- ( a == b ) = 1

  proof
    wva
    wvb
    tb
    wva
    wn
    wvb
    wn
    tb
    wt
    wva
    wvb
    conb
    wcon1.1
    ax-r2
end
