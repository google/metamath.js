include "wn.mm"
include "wo.mm"
include "ax-a5.mm"
include "bi1.mm"

theorem wa5
  param wva: term a
  param wvb: term b


  assert |- ( ( a v ( a ' v b ' ) ' ) == a ) = 1

  proof
    wva
    wva
    wn
    wvb
    wn
    #
    wo
    wn
    wo
    wva
    wva
    @0
    ax-a5
    bi1
end
