include "wa.mm"
include "ancom.mm"
include "bi1.mm"

theorem wancom
  let wva: term a
  let wvb: term b


  assert |- ( ( a ^ b ) == ( b ^ a ) ) = 1

  proof
    wva
    wvb
    wa
    wvb
    wva
    wa
    wva
    wvb
    ancom
    bi1
end
