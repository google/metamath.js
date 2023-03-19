include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cuz.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cfz.mm"
include "cun.mm"
include "wceq.mm"
include "nn0uz.mm"
include "a1i.mm"
include "peano2nn0.mm"
include "syl6eleq.mm"
include "uzsplit.mm"
include "syl.mm"
include "cc.mm"
include "nn0cn.mm"
include "pncan1.mm"
include "oveq2d.mm"
include "uneq1d.mm"
include "3eqtrd.mm"

theorem nn0split
  let cN: class N


  assert |- ( N e. NN0 -> NN0 = ( ( 0 ... N ) u. ( ZZ>= ` ( N + 1 ) ) ) )

  proof
    cN
    cn0
    wcel
    #
    cn0
    cc0
    cuz
    cfv
    #
    cc0
    cN
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    @2
    cuz
    cfv
    #
    cun
    #
    cc0
    cN
    cfz
    co
    #
    @5
    cun
    cn0
    @1
    wceq
    @0
    nn0uz
    a1i
    @0
    @2
    @1
    wcel
    @1
    @6
    wceq
    @0
    @2
    cn0
    @1
    cN
    peano2nn0
    nn0uz
    syl6eleq
    cc0
    @2
    uzsplit
    syl
    @0
    @4
    @7
    @5
    @0
    @3
    cN
    cc0
    cfz
    @0
    cN
    cc
    wcel
    @3
    cN
    wceq
    cN
    nn0cn
    cN
    pncan1
    syl
    oveq2d
    uneq1d
    3eqtrd
end
