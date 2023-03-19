include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cfv.mm"
include "cc.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "lnopli.mm"
include "mp3an1.mm"
include "ax-hvmulid.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "adantr.mm"
include "lnopfi.mm"
include "ffvelrni.mm"
include "syl.mm"
include "3eqtr3d.mm"

theorem lnopaddi
  let cA: class A
  let cB: class B
  let cT: class T
  assume lnopl.1: |- T e. LinOp


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( T ` ( A +h B ) ) = ( ( T ` A ) +h ( T ` B ) ) )

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
    csm
    co
    #
    cB
    cT
    cfv
    #
    cva
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
    cva
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
    lnopl.1
    lnopli
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
    cva
    @0
    @7
    @6
    wceq
    #
    @1
    @0
    @6
    chil
    wcel
    @12
    chil
    chil
    cA
    cT
    cT
    lnopl.1
    lnopfi
    ffvelrni
    @6
    ax-hvmulid
    syl
    adantr
    oveq1d
    3eqtr3d
end
