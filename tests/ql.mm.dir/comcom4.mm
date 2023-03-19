include "wn.mm"
include "comcom3.mm"
include "comcom2.mm"

theorem comcom4
  param wva: term a
  param wvb: term b
  assume comcom.1: |- a C b


  assert |- a ' C b '

  proof
    wva
    wn
    wvb
    wva
    wvb
    comcom.1
    comcom3
    comcom2
end
