include "wdcom.mm"
include "wfh1.mm"

theorem wddi1
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( ( a ^ ( b v c ) ) == ( ( a ^ b ) v ( a ^ c ) ) ) = 1

  proof
    wva
    wvb
    wvc
    wva
    wvb
    wdcom
    wva
    wvc
    wdcom
    wfh1
end
