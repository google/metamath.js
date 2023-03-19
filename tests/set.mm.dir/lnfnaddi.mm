include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cfv.mm"
include "cmul.mm"
include "caddc.mm"
include "cc.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "lnfnli.mm"
include "mp3an1.mm"
include "ax-hvmulid.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "adantr.mm"
include "lnfnfi.mm"
include "ffvelrni.mm"
include "mulid2d.mm"
include "3eqtr3d.mm"

theorem lnfnaddi
  let cA: class A
  let cB: class B
  let cT: class T
  assume lnfnl.1: |- T e. LinFn


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( T ` ( A +h B ) ) = ( ( T ` A ) + ( T ` B ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    c1
    cA
    csm
    co
    #
    cB
    cva
    co
    #
    cT
    cfv
    #
    c1
    cA
    cT
    cfv
    #
    cmul
    co
    #
    cB
    cT
    cfv
    #
    caddc
    co
    #
    cA
    cB
    cva
    co
    #
    cT
    cfv
    #
    @6
    @8
    caddc
    co
    c1
    cc
    wcel
    @0
    @1
    @5
    @9
    wceq
    ax-1cn
    c1
    cA
    cB
    cT
    lnfnl.1
    lnfnli
    mp3an1
    @0
    @5
    @11
    wceq
    @1
    @0
    @4
    @10
    cT
    @0
    @3
    cA
    cB
    cva
    cA
    ax-hvmulid
    oveq1d
    fveq2d
    adantr
    @2
    @7
    @6
    @8
    caddc
    @0
    @7
    @6
    wceq
    @1
    @0
    @6
    chil
    cc
    cA
    cT
    cT
    lnfnl.1
    lnfnfi
    ffvelrni
    mulid2d
    adantr
    oveq1d
    3eqtr3d
end
