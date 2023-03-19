include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "addid1.mm"
include "oveq1d.mm"
include "wceq.mm"
include "0cn.mm"
include "pncan2.mm"
include "mpan2.mm"
include "eqtr3d.mm"

theorem subid
  let cA: class A


  assert |- ( A e. CC -> ( A - A ) = 0 )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    caddc
    co
    #
    cA
    cmin
    co
    #
    cA
    cA
    cmin
    co
    cc0
    @0
    @1
    cA
    cA
    cmin
    cA
    addid1
    oveq1d
    @0
    cc0
    cc
    wcel
    @2
    cc0
    wceq
    0cn
    cA
    cc0
    pncan2
    mpan2
    eqtr3d
end
