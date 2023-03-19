include "wa.mm"
include "wo.mm"
include "wr1.mm"
include "wlan.mm"
include "wa5c.mm"
include "wr2.mm"

theorem wleoa
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume wleoa.1: |- ( ( a v c ) == b ) = 1


  assert |- ( ( a ^ b ) == a ) = 1

  proof
    wva
    wvb
    wa
    wva
    wva
    wvc
    wo
    #
    wa
    wva
    wvb
    @0
    wva
    @0
    wvb
    wleoa.1
    wr1
    wlan
    wva
    wvc
    wa5c
    wr2
end
