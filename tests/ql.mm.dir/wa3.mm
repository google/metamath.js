include "wo.mm"
include "ax-a3.mm"
include "bi1.mm"

theorem wa3
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( ( ( a v b ) v c ) == ( a v ( b v c ) ) ) = 1

  proof
    wva
    wvb
    wo
    wvc
    wo
    wva
    wvb
    wvc
    wo
    wo
    wva
    wvb
    wvc
    ax-a3
    bi1
end
