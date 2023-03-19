include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "ccxp.mm"
include "co.mm"
include "cexp.mm"
include "c1.mm"
include "cn0.mm"
include "wceq.mm"
include "0nn0.mm"
include "cxpexp.mm"
include "mpan2.mm"
include "exp0.mm"
include "eqtrd.mm"

theorem cxp0
  let cA: class A


  assert |- ( A e. CC -> ( A ^c 0 ) = 1 )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    ccxp
    co
    #
    cA
    cc0
    cexp
    co
    #
    c1
    @0
    cc0
    cn0
    wcel
    @1
    @2
    wceq
    0nn0
    cA
    cc0
    cxpexp
    mpan2
    cA
    exp0
    eqtrd
end
