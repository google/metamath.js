include "wt.mm"
include "wa.mm"
include "ancom.mm"
include "an1.mm"
include "ax-r2.mm"

theorem an1r
  let wva: term a


  assert |- ( 1 ^ a ) = a

  proof
    wt
    wva
    wa
    wva
    wt
    wa
    wva
    wt
    wva
    ancom
    wva
    an1
    ax-r2
end
