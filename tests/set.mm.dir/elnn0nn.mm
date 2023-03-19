include "cn0.mm"
include "wcel.mm"
include "cc.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cn.mm"
include "wa.mm"
include "nn0cn.mm"
include "nn0p1nn.mm"
include "jca.mm"
include "cmin.mm"
include "wceq.mm"
include "simpl.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "nnm1nn0.mm"
include "adantl.mm"
include "eqeltrrd.mm"
include "impbii.mm"

theorem elnn0nn
  let cN: class N


  assert |- ( N e. NN0 <-> ( N e. CC /\ ( N + 1 ) e. NN ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    cc
    wcel
    #
    cN
    c1
    caddc
    co
    #
    cn
    wcel
    #
    wa
    #
    @0
    @1
    @3
    cN
    nn0cn
    cN
    nn0p1nn
    jca
    @4
    @2
    c1
    cmin
    co
    #
    cN
    cn0
    @4
    @1
    c1
    cc
    wcel
    @5
    cN
    wceq
    @1
    @3
    simpl
    ax-1cn
    cN
    c1
    pncan
    sylancl
    @3
    @5
    cn0
    wcel
    @1
    @2
    nnm1nn0
    adantl
    eqeltrrd
    impbii
end
