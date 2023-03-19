include "wa.mm"
include "coman1.mm"
include "comcom.mm"

theorem comanr1
  param wva: term a
  param wvb: term b


  assert |- a C ( a ^ b )

  proof
    wva
    wvb
    wa
    wva
    wva
    wvb
    coman1
    comcom
end
