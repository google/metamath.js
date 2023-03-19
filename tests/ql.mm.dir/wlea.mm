include "wa.mm"
include "wo.mm"
include "wa2.mm"
include "wa5b.mm"
include "wr2.mm"
include "wdf-le1.mm"

theorem wlea
  param wva: term a
  param wvb: term b


  assert |- ( ( a ^ b ) =<2 a ) = 1

  proof
    wva
    wvb
    wa
    #
    wva
    @0
    wva
    wo
    wva
    @0
    wo
    wva
    @0
    wva
    wa2
    wva
    wvb
    wa5b
    wr2
    wdf-le1
end
