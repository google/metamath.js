include "wa.mm"
include "anass.mm"
include "bi1.mm"

theorem wanass
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( ( ( a ^ b ) ^ c ) == ( a ^ ( b ^ c ) ) ) = 1

  proof
    wva
    wvb
    wa
    wvc
    wa
    wva
    wvb
    wvc
    wa
    wa
    wva
    wvb
    wvc
    anass
    bi1
end
