include "wn.mm"
include "wo.mm"
include "wa.mm"
include "omlem1.mm"
include "omlem2.mm"
include "wlem3.1.mm"

theorem woml
  param wva: term a
  param wvb: term b


  assert |- ( ( a v ( a ' ^ ( a v b ) ) ) == ( a v b ) ) = 1

  proof
    wva
    wva
    wn
    wva
    wvb
    wo
    #
    wa
    wo
    @0
    wva
    wvb
    omlem1
    wva
    wvb
    omlem2
    wlem3.1
end
