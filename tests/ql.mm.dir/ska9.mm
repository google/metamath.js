include "wn.mm"
include "ax-a1.mm"
include "bi1.mm"

theorem ska9
  param wva: term a


  assert |- ( a == a ' ' ) = 1

  proof
    wva
    wva
    wn
    wn
    wva
    ax-a1
    bi1
end
