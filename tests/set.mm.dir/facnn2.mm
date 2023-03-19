include "cn.mm"
include "wcel.mm"
include "cc.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cn0.mm"
include "wa.mm"
include "cfa.mm"
include "cfv.mm"
include "cmul.mm"
include "wceq.mm"
include "elnnnn0.mm"
include "caddc.mm"
include "facp1.mm"
include "adantl.mm"
include "npcan1.mm"
include "fveq2d.mm"
include "adantr.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "sylbi.mm"

theorem facnn2
  let cN: class N


  assert |- ( N e. NN -> ( ! ` N ) = ( ( ! ` ( N - 1 ) ) x. N ) )

  proof
    cN
    cn
    wcel
    cN
    cc
    wcel
    #
    cN
    c1
    cmin
    co
    #
    cn0
    wcel
    #
    wa
    #
    cN
    cfa
    cfv
    #
    @1
    cfa
    cfv
    #
    cN
    cmul
    co
    #
    wceq
    cN
    elnnnn0
    @3
    @1
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    @5
    @7
    cmul
    co
    #
    @4
    @6
    @2
    @8
    @9
    wceq
    @0
    @1
    facp1
    adantl
    @0
    @8
    @4
    wceq
    @2
    @0
    @7
    cN
    cfa
    cN
    npcan1
    #
    fveq2d
    adantr
    @0
    @9
    @6
    wceq
    @2
    @0
    @7
    cN
    @5
    cmul
    @10
    oveq2d
    adantr
    3eqtr3d
    sylbi
end
