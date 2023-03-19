include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "cmin.mm"
include "df-neg.mm"
include "oveq2i.mm"
include "wceq.mm"
include "0cn.mm"
include "pncan3.mm"
include "mpan2.mm"
include "syl5eq.mm"

theorem negid
  let cA: class A


  assert |- ( A e. CC -> ( A + -u A ) = 0 )

  proof
    cA
    cc
    wcel
    #
    cA
    cA
    cneg
    #
    caddc
    co
    cA
    cc0
    cA
    cmin
    co
    #
    caddc
    co
    #
    cc0
    @1
    @2
    cA
    caddc
    cA
    df-neg
    oveq2i
    @0
    cc0
    cc
    wcel
    @3
    cc0
    wceq
    0cn
    cA
    cc0
    pncan3
    mpan2
    syl5eq
end
