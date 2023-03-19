include "tb.mm"
include "wn.mm"
include "conb.mm"
include "bi1.mm"

theorem wcon
  param wva: term a
  param wvb: term b


  assert |- ( ( a == b ) == ( a ' == b ' ) ) = 1

  proof
    wva
    wvb
    tb
    wva
    wn
    wvb
    wn
    tb
    wva
    wvb
    conb
    bi1
end
