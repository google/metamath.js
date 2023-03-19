include "wa.mm"
include "lea.mm"
include "lecom.mm"

theorem coman1
  param wva: term a
  param wvb: term b


  assert |- ( a ^ b ) C a

  proof
    wva
    wvb
    wa
    wva
    wva
    wvb
    lea
    lecom
end
