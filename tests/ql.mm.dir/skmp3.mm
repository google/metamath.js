include "wi3.mm"
include "wn.mm"
include "wo.mm"
include "ska15.mm"
include "skr0.mm"

theorem skmp3
  param wva: term a
  param wvb: term b
  assume skmp3.1: |- a = 1
  assume skmp3.2: |- ( a ->3 b ) = 1


  assert |- b = 1

  proof
    wva
    wvb
    skmp3.1
    wva
    wvb
    wi3
    wva
    wn
    wvb
    wo
    skmp3.2
    wva
    wvb
    ska15
    skr0
    skr0
end
