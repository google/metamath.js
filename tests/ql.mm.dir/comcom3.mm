include "wn.mm"
include "comcom.mm"
include "comcom2.mm"

theorem comcom3
  let wva: term a
  let wvb: term b
  assume comcom.1: |- a C b


  assert |- a ' C b

  proof
    wvb
    wva
    wn
    wvb
    wva
    wva
    wvb
    comcom.1
    comcom
    comcom2
    comcom
end
