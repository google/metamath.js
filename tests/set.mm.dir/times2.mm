include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "2cn.mm"
include "mulcom.mm"
include "mpan2.mm"
include "2times.mm"
include "eqtrd.mm"

theorem times2
  let cA: class A


  assert |- ( A e. CC -> ( A x. 2 ) = ( A + A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    c2
    cmul
    co
    #
    c2
    cA
    cmul
    co
    #
    cA
    cA
    caddc
    co
    @0
    c2
    cc
    wcel
    @1
    @2
    wceq
    2cn
    cA
    c2
    mulcom
    mpan2
    cA
    2times
    eqtrd
end
