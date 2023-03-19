include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "mulcom.mm"
include "mpan.mm"
include "mulid1.mm"
include "eqtrd.mm"

theorem mulid2
  let cA: class A


  assert |- ( A e. CC -> ( 1 x. A ) = A )

  proof
    cA
    cc
    wcel
    #
    c1
    cA
    cmul
    co
    #
    cA
    c1
    cmul
    co
    #
    cA
    c1
    cc
    wcel
    @0
    @1
    @2
    wceq
    ax-1cn
    c1
    cA
    mulcom
    mpan
    cA
    mulid1
    eqtrd
end
