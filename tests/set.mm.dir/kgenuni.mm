include "ctop.mm"
include "wcel.mm"
include "ckgen.mm"
include "cfv.mm"
include "ctopon.mm"
include "cuni.mm"
include "wceq.mm"
include "toptopon.mm"
include "kgentopon.mm"
include "sylbi.mm"
include "toponuni.mm"
include "syl.mm"

theorem kgenuni
  let cJ: class J
  let cX: class X
  assume kgenuni.1: |- X = U. J


  assert |- ( J e. Top -> X = U. ( kGen ` J ) )

  proof
    cJ
    ctop
    wcel
    #
    cJ
    ckgen
    cfv
    #
    cX
    ctopon
    cfv
    #
    wcel
    #
    cX
    @1
    cuni
    wceq
    @0
    cJ
    @2
    wcel
    @3
    cJ
    cX
    kgenuni.1
    toptopon
    cJ
    cX
    kgentopon
    sylbi
    cX
    @1
    toponuni
    syl
end
