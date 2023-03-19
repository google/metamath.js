include "tb.mm"
include "bicom.mm"
include "bi1.mm"

theorem ska12
  param wva: term a
  param wvb: term b


  assert |- ( ( a == b ) == ( b == a ) ) = 1

  proof
    wva
    wvb
    tb
    wvb
    wva
    tb
    wva
    wvb
    bicom
    bi1
end
