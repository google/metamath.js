include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cn0.mm"
include "wceq.mm"
include "2nn0.mm"
include "absexp.mm"
include "mpan2.mm"
include "eqcomd.mm"

theorem abssq
  let cA: class A


  assert |- ( A e. CC -> ( ( abs ` A ) ^ 2 ) = ( abs ` ( A ^ 2 ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    c2
    cexp
    co
    cabs
    cfv
    #
    cA
    cabs
    cfv
    c2
    cexp
    co
    #
    @0
    c2
    cn0
    wcel
    @1
    @2
    wceq
    2nn0
    cA
    c2
    absexp
    mpan2
    eqcomd
end
