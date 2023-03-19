include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cn0.mm"
include "nn1m1nn.mm"
include "oveq1.mm"
include "1m1e0.mm"
include "syl6eq.mm"
include "orim1i.mm"
include "syl.mm"
include "orcomd.mm"
include "elnn0.mm"
include "sylibr.mm"

theorem nnm1nn0
  let cN: class N


  assert |- ( N e. NN -> ( N - 1 ) e. NN0 )

  proof
    cN
    cn
    wcel
    #
    cN
    c1
    cmin
    co
    #
    cn
    wcel
    #
    @1
    cc0
    wceq
    #
    wo
    @1
    cn0
    wcel
    @0
    @3
    @2
    @0
    cN
    c1
    wceq
    #
    @2
    wo
    @3
    @2
    wo
    cN
    nn1m1nn
    @4
    @3
    @2
    @4
    @1
    c1
    c1
    cmin
    co
    cc0
    cN
    c1
    c1
    cmin
    oveq1
    1m1e0
    syl6eq
    orim1i
    syl
    orcomd
    @1
    elnn0
    sylibr
end
