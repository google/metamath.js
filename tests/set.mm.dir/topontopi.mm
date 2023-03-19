include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ctop.mm"
include "topontop.mm"
include "ax-mp.mm"

theorem topontopi
  let cB: class B
  let cJ: class J
  assume topontopi.1: |- J e. ( TopOn ` B )


  assert |- J e. Top

  proof
    cJ
    cB
    ctopon
    cfv
    wcel
    cJ
    ctop
    wcel
    topontopi.1
    cB
    cJ
    topontop
    ax-mp
end
