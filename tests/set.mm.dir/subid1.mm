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
include "pncan.mm"
include "mpan2.mm"
include "eqtr3d.mm"

theorem subid1
  let cA: class A


  assert |- ( A e. CC -> ( A - 0 ) = A )

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
    cc0
    cmin
    co
    #
    cA
    cc0
    cmin
    co
    cA
    @0
    @1
    cA
    cc0
    cmin
    cA
    addid1
    oveq1d
    @0
    cc0
    cc
    wcel
    @2
    cA
    wceq
    0cn
    cA
    cc0
    pncan
    mpan2
    eqtr3d
end
