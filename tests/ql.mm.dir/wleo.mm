include "wo.mm"
include "wa5c.mm"
include "wdf2le1.mm"

theorem wleo
  let wva: term a
  let wvb: term b


  assert |- ( a =<2 ( a v b ) ) = 1

  proof
    wva
    wva
    wvb
    wo
    wva
    wvb
    wa5c
    wdf2le1
end
