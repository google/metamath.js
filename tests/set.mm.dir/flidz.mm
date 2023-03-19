include "cr.mm"
include "wcel.mm"
include "cfl.mm"
include "cfv.mm"
include "wceq.mm"
include "cz.mm"
include "flcl.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "flid.mm"
include "impbid1.mm"

theorem flidz
  let cA: class A


  assert |- ( A e. RR -> ( ( |_ ` A ) = A <-> A e. ZZ ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cfl
    cfv
    #
    cA
    wceq
    #
    cA
    cz
    wcel
    #
    @0
    @1
    cz
    wcel
    @2
    @3
    cA
    flcl
    @1
    cA
    cz
    eleq1
    syl5ibcom
    cA
    flid
    impbid1
end
