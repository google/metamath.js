include "cr.mm"
include "wcel.mm"
include "cfl.mm"
include "cfv.mm"
include "cz.mm"
include "wceq.mm"
include "flcl.mm"
include "flid.mm"
include "syl.mm"

theorem flidm
  let cA: class A


  assert |- ( A e. RR -> ( |_ ` ( |_ ` A ) ) = ( |_ ` A ) )

  proof
    cA
    cr
    wcel
    cA
    cfl
    cfv
    #
    cz
    wcel
    @0
    cfl
    cfv
    @0
    wceq
    cA
    flcl
    @0
    flid
    syl
end
