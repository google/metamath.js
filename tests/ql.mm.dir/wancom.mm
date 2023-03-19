include "wa.mm"
include "ancom.mm"
include "bi1.mm"

theorem wancom
  param wva: term a
  param wvb: term b


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
