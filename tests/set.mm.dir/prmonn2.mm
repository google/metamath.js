include "cn.mm"
include "wcel.mm"
include "cprmo.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "cprime.mm"
include "cmul.mm"
include "cif.mm"
include "cc.mm"
include "wceq.mm"
include "nncn.mm"
include "npcan1.mm"
include "syl.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "prmop1.mm"
include "eleq1d.mm"
include "oveq2d.mm"
include "ifbieq1d.mm"
include "3eqtrd.mm"

theorem prmonn2
  let cN: class N


  assert |- ( N e. NN -> ( #p ` N ) = if ( N e. Prime , ( ( #p ` ( N - 1 ) ) x. N ) , ( #p ` ( N - 1 ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cN
    cprmo
    cfv
    cN
    c1
    cmin
    co
    #
    c1
    caddc
    co
    #
    cprmo
    cfv
    #
    @2
    cprime
    wcel
    #
    @1
    cprmo
    cfv
    #
    @2
    cmul
    co
    #
    @5
    cif
    #
    cN
    cprime
    wcel
    #
    @5
    cN
    cmul
    co
    #
    @5
    cif
    @0
    cN
    @2
    cprmo
    @0
    @2
    cN
    @0
    cN
    cc
    wcel
    @2
    cN
    wceq
    cN
    nncn
    cN
    npcan1
    syl
    #
    eqcomd
    fveq2d
    @0
    @1
    cn0
    wcel
    @3
    @7
    wceq
    cN
    nnm1nn0
    @1
    prmop1
    syl
    @0
    @4
    @8
    @6
    @9
    @5
    @0
    @2
    cN
    cprime
    @10
    eleq1d
    @0
    @2
    cN
    @5
    cmul
    @10
    oveq2d
    ifbieq1d
    3eqtrd
end
