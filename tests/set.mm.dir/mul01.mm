include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "0cn.mm"
include "mulcom.mm"
include "mpan2.mm"
include "mul02.mm"
include "eqtrd.mm"

theorem mul01
  let cA: class A


  assert |- ( A e. CC -> ( A x. 0 ) = 0 )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    cmul
    co
    #
    cc0
    cA
    cmul
    co
    #
    cc0
    @0
    cc0
    cc
    wcel
    @1
    @2
    wceq
    0cn
    cA
    cc0
    mulcom
    mpan2
    cA
    mul02
    eqtrd
end
