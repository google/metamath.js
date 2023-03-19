include "cnpi.mm"
include "wcel.mm"
include "wa.mm"
include "cpli.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "addclpi.mm"
include "eleq1.mm"
include "syl5ib.mm"
include "imp.mm"
include "dmaddpi.mm"
include "0npi.mm"
include "ndmovrcl.mm"
include "simpr.mm"
include "3syl.mm"
include "coa.mm"
include "addpiord.mm"
include "adantr.mm"
include "adantlr.mm"
include "eqeq12d.mm"
include "com.mm"
include "pinn.mm"
include "w3a.mm"
include "nnacan.mm"
include "biimpd.mm"
include "syl3an.mm"
include "3expa.mm"
include "sylbid.mm"
include "sylan2.mm"
include "exp32.mm"
include "imp4b.mm"
include "pm2.43i.mm"
include "ex.mm"
include "oveq2.mm"
include "impbid1.mm"

theorem addcanpi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. N. /\ B e. N. ) -> ( ( A +N B ) = ( A +N C ) <-> B = C ) )

  proof
    cA
    cnpi
    wcel
    #
    cB
    cnpi
    wcel
    #
    wa
    #
    cA
    cB
    cpli
    co
    #
    cA
    cC
    cpli
    co
    #
    wceq
    #
    cB
    cC
    wceq
    #
    @2
    @5
    @6
    @2
    @5
    wa
    @6
    @2
    @5
    @2
    @5
    @6
    @2
    @5
    @2
    @5
    @6
    wi
    #
    @5
    @2
    wa
    #
    @2
    cC
    cnpi
    wcel
    #
    @7
    @8
    @4
    cnpi
    wcel
    #
    @0
    @9
    wa
    @9
    @5
    @2
    @10
    @2
    @3
    cnpi
    wcel
    @5
    @10
    cA
    cB
    addclpi
    @3
    @4
    cnpi
    eleq1
    syl5ib
    imp
    cA
    cC
    cnpi
    cpli
    dmaddpi
    0npi
    ndmovrcl
    @0
    @9
    simpr
    3syl
    @2
    @9
    wa
    #
    @5
    cA
    cB
    coa
    co
    #
    cA
    cC
    coa
    co
    #
    wceq
    #
    @6
    @11
    @3
    @12
    @4
    @13
    @2
    @3
    @12
    wceq
    @9
    cA
    cB
    addpiord
    adantr
    @0
    @9
    @4
    @13
    wceq
    @1
    cA
    cC
    addpiord
    adantlr
    eqeq12d
    @0
    @1
    @9
    @14
    @6
    wi
    #
    @0
    cA
    com
    wcel
    #
    @1
    cB
    com
    wcel
    #
    @9
    cC
    com
    wcel
    #
    @15
    cA
    pinn
    cB
    pinn
    cC
    pinn
    @16
    @17
    @18
    w3a
    @14
    @6
    cA
    cB
    cC
    nnacan
    biimpd
    syl3an
    3expa
    sylbid
    sylan2
    exp32
    imp4b
    pm2.43i
    ex
    cB
    cC
    cA
    cpli
    oveq2
    impbid1
end
