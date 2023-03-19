include "cc.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "cexp.mm"
include "cmul.mm"
include "wceq.mm"
include "nncn.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "adantl.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "expp1.mm"
include "sylan2.mm"
include "eqtr3d.mm"

theorem expm1t
  let cA: class A
  let cN: class N


  assert |- ( ( A e. CC /\ N e. NN ) -> ( A ^ N ) = ( ( A ^ ( N - 1 ) ) x. A ) )

  proof
    cA
    cc
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    cA
    cN
    c1
    cmin
    co
    #
    c1
    caddc
    co
    #
    cexp
    co
    #
    cA
    cN
    cexp
    co
    #
    cA
    @2
    cexp
    co
    cA
    cmul
    co
    #
    @1
    @4
    @5
    wceq
    @0
    @1
    @3
    cN
    cA
    cexp
    @1
    cN
    cc
    wcel
    c1
    cc
    wcel
    @3
    cN
    wceq
    cN
    nncn
    ax-1cn
    cN
    c1
    npcan
    sylancl
    oveq2d
    adantl
    @1
    @0
    @2
    cn0
    wcel
    @4
    @6
    wceq
    cN
    nnm1nn0
    cA
    @2
    expp1
    sylan2
    eqtr3d
end
