include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "mulneg1.mm"
include "mpan.mm"
include "mulid2.mm"
include "negeqd.mm"
include "eqtrd.mm"

theorem mulm1
  let cA: class A


  assert |- ( A e. CC -> ( -u 1 x. A ) = -u A )

  proof
    cA
    cc
    wcel
    #
    c1
    cneg
    cA
    cmul
    co
    #
    c1
    cA
    cmul
    co
    #
    cneg
    #
    cA
    cneg
    c1
    cc
    wcel
    @0
    @1
    @3
    wceq
    ax-1cn
    c1
    cA
    mulneg1
    mpan
    @0
    @2
    cA
    cA
    mulid2
    negeqd
    eqtrd
end
