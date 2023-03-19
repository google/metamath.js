include "wa.mm"
include "ancom.mm"
include "coman1.mm"
include "bctr.mm"

theorem coman2
  let wva: term a
  let wvb: term b


  assert |- ( a ^ b ) C b

  proof
    wva
    wvb
    wa
    wvb
    wva
    wa
    wvb
    wva
    wvb
    ancom
    wvb
    wva
    coman1
    bctr
end
