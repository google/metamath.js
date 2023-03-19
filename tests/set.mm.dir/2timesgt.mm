include "crp.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "clt.mm"
include "rpre.mm"
include "id.mm"
include "ltaddrp2d.mm"
include "cc.mm"
include "wceq.mm"
include "rpcn.mm"
include "2times.mm"
include "eqcomd.mm"
include "syl.mm"
include "breqtrd.mm"

theorem 2timesgt
  let cA: class A


  assert |- ( A e. RR+ -> A < ( 2 x. A ) )

  proof
    cA
    crp
    wcel
    #
    cA
    cA
    cA
    caddc
    co
    #
    c2
    cA
    cmul
    co
    #
    clt
    @0
    cA
    cA
    cA
    rpre
    @0
    id
    ltaddrp2d
    @0
    cA
    cc
    wcel
    #
    @1
    @2
    wceq
    cA
    rpcn
    @3
    @2
    @1
    cA
    2times
    eqcomd
    syl
    breqtrd
end
