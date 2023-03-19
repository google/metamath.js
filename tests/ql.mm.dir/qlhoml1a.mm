include "wn.mm"
include "ax-a1.mm"
include "bile.mm"

theorem qlhoml1a
  param wva: term a


  assert |- a =< a ' '

  proof
    wva
    wva
    wn
    wn
    wva
    ax-a1
    bile
end
