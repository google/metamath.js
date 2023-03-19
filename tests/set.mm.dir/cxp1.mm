include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "ccxp.mm"
include "co.mm"
include "cexp.mm"
include "cn0.mm"
include "wceq.mm"
include "1nn0.mm"
include "cxpexp.mm"
include "mpan2.mm"
include "exp1.mm"
include "eqtrd.mm"

theorem cxp1
  let cA: class A


  assert |- ( A e. CC -> ( A ^c 1 ) = A )

  proof
    cA
    cc
    wcel
    #
    cA
    c1
    ccxp
    co
    #
    cA
    c1
    cexp
    co
    #
    cA
    @0
    c1
    cn0
    wcel
    @1
    @2
    wceq
    1nn0
    cA
    c1
    cxpexp
    mpan2
    cA
    exp1
    eqtrd
end
