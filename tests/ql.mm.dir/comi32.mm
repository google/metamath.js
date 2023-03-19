include "comid.mm"
include "com2i3.mm"

theorem comi32
  let wva: term a
  let wvb: term b
  assume comi32.1: |- a C b


  assert |- a C ( b ->3 a )

  proof
    wva
    wvb
    wva
    comi32.1
    wva
    comid
    com2i3
end
