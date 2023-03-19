include "wo.mm"
include "leo.mm"
include "lei3.mm"

theorem bina3
  let wva: term a
  let wvb: term b


  assert |- ( a ->3 ( a v b ) ) = 1

  proof
    wva
    wva
    wvb
    wo
    wva
    wvb
    leo
    lei3
end
