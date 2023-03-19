include "wn.mm"
include "wo.mm"
include "wa.mm"
include "omlem1.mm"
include "omlem2.mm"
include "lem3.1.mm"

theorem oml
  param wva: term a
  param wvb: term b


  assert |- ( a v ( a ' ^ ( a v b ) ) ) = ( a v b )

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
    lem3.1
end
