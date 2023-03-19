include "wn.mm"
include "wo.mm"
include "ax-a4.mm"
include "bi1.mm"

theorem wa4
  param wva: term a
  param wvb: term b


  assert |- ( ( a v ( b v b ' ) ) == ( b v b ' ) ) = 1

  proof
    wva
    wvb
    wvb
    wn
    wo
    #
    wo
    @0
    wva
    wvb
    ax-a4
    bi1
end
