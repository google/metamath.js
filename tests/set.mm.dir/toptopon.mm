include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ctop.mm"
include "cuni.mm"
include "wceq.mm"
include "istopon.mm"
include "mpbiran2.mm"
include "bicomi.mm"

theorem toptopon
  let cJ: class J
  let cX: class X
  assume toptopon.1: |- X = U. J


  assert |- ( J e. Top <-> J e. ( TopOn ` X ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cJ
    ctop
    wcel
    #
    @0
    @1
    cX
    cJ
    cuni
    wceq
    toptopon.1
    cX
    cJ
    istopon
    mpbiran2
    bicomi
end
