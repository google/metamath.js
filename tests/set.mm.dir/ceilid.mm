include "cz.mm"
include "wcel.mm"
include "cceil.mm"
include "cfv.mm"
include "cneg.mm"
include "cfl.mm"
include "cr.mm"
include "wceq.mm"
include "zre.mm"
include "ceilval.mm"
include "syl.mm"
include "znegcl.mm"
include "flid.mm"
include "negeqd.mm"
include "zcn.mm"
include "negnegd.mm"
include "3eqtrd.mm"

theorem ceilid
  let cA: class A


  assert |- ( A e. ZZ -> ( |^ ` A ) = A )

  proof
    cA
    cz
    wcel
    #
    cA
    cceil
    cfv
    #
    cA
    cneg
    #
    cfl
    cfv
    #
    cneg
    #
    @2
    cneg
    cA
    @0
    cA
    cr
    wcel
    @1
    @4
    wceq
    cA
    zre
    cA
    ceilval
    syl
    @0
    @3
    @2
    @0
    @2
    cz
    wcel
    @3
    @2
    wceq
    cA
    znegcl
    @2
    flid
    syl
    negeqd
    @0
    cA
    cA
    zcn
    negnegd
    3eqtrd
end
