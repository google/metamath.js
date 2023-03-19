include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "df-neg.mm"
include "wceq.mm"
include "0cn.mm"
include "subneg.mm"
include "mpan.mm"
include "syl5eq.mm"
include "addid2.mm"
include "eqtrd.mm"

theorem negneg
  let cA: class A


  assert |- ( A e. CC -> -u -u A = A )

  proof
    cA
    cc
    wcel
    #
    cA
    cneg
    #
    cneg
    #
    cc0
    cA
    caddc
    co
    #
    cA
    @0
    @2
    cc0
    @1
    cmin
    co
    #
    @3
    @1
    df-neg
    cc0
    cc
    wcel
    @0
    @4
    @3
    wceq
    0cn
    cc0
    cA
    subneg
    mpan
    syl5eq
    cA
    addid2
    eqtrd
end
