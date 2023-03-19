include "chmph.mm"
include "wbr.mm"
include "ctop.mm"
include "wcel.mm"
include "hmphtop.mm"
include "simpld.mm"

theorem hmphtop1
  let cJ: class J
  let cK: class K


  assert |- ( J ~= K -> J e. Top )

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
    simpld
end
