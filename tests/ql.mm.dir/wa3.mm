include "wo.mm"
include "ax-a3.mm"
include "bi1.mm"

theorem wa3
  let wva: term a
  let wvb: term b
  let wvc: term c


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
