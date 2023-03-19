include "cr.mm"
include "wcel.mm"
include "cceil.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cneg.mm"
include "cfl.mm"
include "clt.mm"
include "ceilval.mm"
include "oveq1d.mm"
include "ceim1l.mm"
include "eqbrtrd.mm"

theorem ceilm1lt
  let cA: class A


  assert |- ( A e. RR -> ( ( |^ ` A ) - 1 ) < A )

  proof
    cA
    cr
    wcel
    #
    cA
    cceil
    cfv
    #
    c1
    cmin
    co
    cA
    cneg
    cfl
    cfv
    cneg
    #
    c1
    cmin
    co
    cA
    clt
    @0
    @1
    @2
    c1
    cmin
    cA
    ceilval
    oveq1d
    cA
    ceim1l
    eqbrtrd
end
