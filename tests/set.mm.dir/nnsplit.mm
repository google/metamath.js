include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cfz.mm"
include "cun.mm"
include "wceq.mm"
include "nnuz.mm"
include "a1i.mm"
include "peano2nn.mm"
include "syl6eleq.mm"
include "uzsplit.mm"
include "syl.mm"
include "nncn.mm"
include "1cnd.mm"
include "pncand.mm"
include "oveq2d.mm"
include "uneq1d.mm"
include "3eqtrd.mm"

theorem nnsplit
  let cN: class N


  assert |- ( N e. NN -> NN = ( ( 1 ... N ) u. ( ZZ>= ` ( N + 1 ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cn
    c1
    cuz
    cfv
    #
    c1
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
    c1
    cN
    cfz
    co
    #
    @5
    cun
    cn
    @1
    wceq
    @0
    nnuz
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
    cn
    @1
    cN
    peano2nn
    nnuz
    syl6eleq
    c1
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
    c1
    cfz
    @0
    cN
    c1
    cN
    nncn
    @0
    1cnd
    pncand
    oveq2d
    uneq1d
    3eqtrd
end
