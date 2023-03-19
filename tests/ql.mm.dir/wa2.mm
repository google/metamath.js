include "wo.mm"
include "ax-a2.mm"
include "bi1.mm"

theorem wa2
  param wva: term a
  param wvb: term b


  assert |- ( ( a v b ) == ( b v a ) ) = 1

  proof
    wva
    wvb
    wo
    wvb
    wva
    wo
    wva
    wvb
    ax-a2
    bi1
end
