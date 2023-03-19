include "tb.mm"
include "wn.mm"
include "bicom.mm"
include "conb.mm"
include "ax-r2.mm"

theorem nomcon5
  param wva: term a
  param wvb: term b


  assert |- ( a == b ) = ( b ' == a ' )

  proof
    wva
    wvb
    tb
    wvb
    wva
    tb
    wvb
    wn
    wva
    wn
    tb
    wva
    wvb
    bicom
    wvb
    wva
    conb
    ax-r2
end
