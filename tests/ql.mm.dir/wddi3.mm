include "wdcom.mm"
include "wfh3.mm"

theorem wddi3
  let wva: term a
  let wvb: term b
  let wvc: term c


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
