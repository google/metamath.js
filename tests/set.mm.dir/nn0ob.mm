include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cmin.mm"
include "nn0o.mm"
include "wa.mm"
include "wceq.mm"
include "cc.mm"
include "nn0cn.mm"
include "xp1d2m1eqxm1d2.mm"
include "eqcomd.mm"
include "syl.mm"
include "peano2cnm.mm"
include "halfcld.mm"
include "1cnd.mm"
include "peano2nn0.mm"
include "nn0cnd.mm"
include "addlsub.mm"
include "mpbird.mm"
include "adantr.mm"
include "adantl.mm"
include "eqeltrrd.mm"
include "impbida.mm"

theorem nn0ob
  let cN: class N


  assert |- ( N e. NN0 -> ( ( ( N + 1 ) / 2 ) e. NN0 <-> ( ( N - 1 ) / 2 ) e. NN0 ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cn0
    wcel
    cN
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cn0
    wcel
    #
    cN
    nn0o
    @0
    @5
    wa
    @4
    c1
    caddc
    co
    #
    @2
    cn0
    @0
    @6
    @2
    wceq
    #
    @5
    @0
    @7
    @4
    @2
    c1
    cmin
    co
    #
    wceq
    #
    @0
    cN
    cc
    wcel
    #
    @9
    cN
    nn0cn
    #
    @10
    @8
    @4
    cN
    xp1d2m1eqxm1d2
    eqcomd
    syl
    @0
    @4
    c1
    @2
    @0
    @3
    @0
    @10
    @3
    cc
    wcel
    @11
    cN
    peano2cnm
    syl
    halfcld
    @0
    1cnd
    @0
    @1
    @0
    @1
    cN
    peano2nn0
    nn0cnd
    halfcld
    addlsub
    mpbird
    adantr
    @5
    @6
    cn0
    wcel
    @0
    @4
    peano2nn0
    adantl
    eqeltrrd
    impbida
end
