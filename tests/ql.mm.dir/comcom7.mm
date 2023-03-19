include "wn.mm"
include "comcom3.mm"
include "comcom5.mm"

theorem comcom7
  let wva: term a
  let wvb: term b
  assume comcom7.1: |- a C b '


  assert |- a C b

  proof
    wva
    wvb
    wva
    wvb
    wn
    comcom7.1
    comcom3
    comcom5
end
