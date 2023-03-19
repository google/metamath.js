include "cc0.mm"
include "cdp2.mm"
include "cdp.mm"
include "co.mm"
include "c1.mm"
include "cdc.mm"
include "cmul.mm"
include "cexp.mm"
include "0p1e1.mm"
include "0z.mm"
include "1z.mm"
include "dpexpp1.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "10nn0.mm"
include "nn0cni.mm"
include "exp0.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "exp1.mm"
include "3eqtr3ri.mm"
include "crp.mm"
include "rpdpcl.mm"
include "rpcn.mm"
include "mulid1.mm"
include "eqtri.mm"

theorem 0dp2dp
  let cA: class A
  let cB: class B
  assume 0dp2dp.a: |- A e. NN0
  assume 0dp2dp.b: |- B e. RR+


  assert |- ( ( 0 . _ A B ) x. ; 1 0 ) = ( A . B )

  proof
    cc0
    cA
    cB
    cdp2
    cdp
    co
    #
    c1
    cc0
    cdc
    #
    cmul
    co
    #
    cA
    cB
    cdp
    co
    #
    c1
    cmul
    co
    #
    @3
    @3
    @1
    cc0
    cexp
    co
    #
    cmul
    co
    @0
    @1
    c1
    cexp
    co
    #
    cmul
    co
    @4
    @2
    cA
    cB
    cc0
    c1
    0dp2dp.a
    0dp2dp.b
    0p1e1
    0z
    1z
    dpexpp1
    @5
    c1
    @3
    cmul
    @1
    cc
    wcel
    #
    @5
    c1
    wceq
    @1
    10nn0
    nn0cni
    #
    @1
    exp0
    ax-mp
    oveq2i
    @6
    @1
    @0
    cmul
    @7
    @6
    @1
    wceq
    @8
    @1
    exp1
    ax-mp
    oveq2i
    3eqtr3ri
    @3
    cc
    wcel
    #
    @4
    @3
    wceq
    @3
    crp
    wcel
    @9
    cA
    cB
    0dp2dp.a
    0dp2dp.b
    rpdpcl
    @3
    rpcn
    ax-mp
    @3
    mulid1
    ax-mp
    eqtri
end
