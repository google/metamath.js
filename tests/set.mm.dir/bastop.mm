include "ctb.mm"
include "wcel.mm"
include "ctop.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "tgtop.mm"
include "tgcl.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "impbid2.mm"

theorem bastop
  let cB: class B


  assert |- ( B e. TopBases -> ( B e. Top <-> ( topGen ` B ) = B ) )

  proof
    cB
    ctb
    wcel
    #
    cB
    ctop
    wcel
    #
    cB
    ctg
    cfv
    #
    cB
    wceq
    #
    cB
    tgtop
    @0
    @2
    ctop
    wcel
    @3
    @1
    cB
    tgcl
    @2
    cB
    ctop
    eleq1
    syl5ibcom
    impbid2
end
