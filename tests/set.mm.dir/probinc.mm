include "cprb.mm"
include "wcel.mm"
include "cdm.mm"
include "w3a.mm"
include "wss.mm"
include "wa.mm"
include "cmeas.mm"
include "cfv.mm"
include "simpl1.mm"
include "domprobmeas.mm"
include "syl.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr.mm"
include "measssd.mm"

theorem probinc
  let cA: class A
  let cB: class B
  let cP: class P


  assert |- ( ( ( P e. Prob /\ A e. dom P /\ B e. dom P ) /\ A C_ B ) -> ( P ` A ) <_ ( P ` B ) )

  proof
    cP
    cprb
    wcel
    #
    cA
    cP
    cdm
    #
    wcel
    #
    cB
    @1
    wcel
    #
    w3a
    #
    cA
    cB
    wss
    #
    wa
    #
    cA
    cB
    @1
    cP
    @6
    @0
    cP
    @1
    cmeas
    cfv
    wcel
    @0
    @2
    @3
    @5
    simpl1
    cP
    domprobmeas
    syl
    @0
    @2
    @3
    @5
    simpl2
    @0
    @2
    @3
    @5
    simpl3
    @4
    @5
    simpr
    measssd
end
