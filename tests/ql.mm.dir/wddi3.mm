include "wdcom.mm"
include "wfh3.mm"

theorem wddi3
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( ( a v ( b ^ c ) ) == ( ( a v b ) ^ ( a v c ) ) ) = 1

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
    wfh3
end
