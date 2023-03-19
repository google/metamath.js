include "cr.mm"
include "wcel.mm"
include "cneg.mm"
include "cfl.mm"
include "cfv.mm"
include "renegcl.mm"
include "flcld.mm"
include "znegcld.mm"

theorem ceicl
  let cA: class A


  assert |- ( A e. RR -> -u ( |_ ` -u A ) e. ZZ )

  proof
    cA
    cr
    wcel
    #
    cA
    cneg
    #
    cfl
    cfv
    @0
    @1
    cA
    renegcl
    flcld
    znegcld
end
