include "wi1.mm"
include "wn.mm"
include "wo.mm"
include "wt.mm"
include "lecom.mm"
include "u1lemc4.mm"
include "sklem.mm"
include "ax-r2.mm"

theorem u1lemle1
  param wva: term a
  param wvb: term b
  assume ulemle1.1: |- a =< b


  assert |- ( a ->1 b ) = 1

  proof
    wva
    wvb
    wi1
    wva
    wn
    wvb
    wo
    wt
    wva
    wvb
    wva
    wvb
    ulemle1.1
    lecom
    u1lemc4
    wva
    wvb
    ulemle1.1
    sklem
    ax-r2
end
