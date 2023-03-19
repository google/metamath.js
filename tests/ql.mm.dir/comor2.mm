include "wo.mm"
include "ax-a2.mm"
include "comor1.mm"
include "bctr.mm"

theorem comor2
  param wva: term a
  param wvb: term b


  assert |- ( a v b ) C b

  proof
    wva
    wvb
    wo
    wvb
    wva
    wo
    wvb
    wva
    wvb
    ax-a2
    wvb
    wva
    comor1
    bctr
end
