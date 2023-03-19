include "wa.mm"
include "coman2.mm"
include "comcom.mm"

theorem comanr2
  let wva: term a
  let wvb: term b


  assert |- b C ( a ^ b )

  proof
    wva
    wvb
    wa
    wvb
    wva
    wvb
    coman2
    comcom
end
