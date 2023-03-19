include "chmph.mm"
include "wbr.mm"
include "ctop.mm"
include "wcel.mm"
include "hmphtop.mm"
include "simprd.mm"

theorem hmphtop2
  let cJ: class J
  let cK: class K


  assert |- ( J ~= K -> K e. Top )

  proof
    cJ
    cK
    chmph
    wbr
    cJ
    ctop
    wcel
    cK
    ctop
    wcel
    cJ
    cK
    hmphtop
    simprd
end
