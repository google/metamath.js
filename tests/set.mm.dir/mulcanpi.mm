include "cnpi.mm"
include "wcel.mm"
include "wa.mm"
include "cmi.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "mulclpi.mm"
include "eleq1.mm"
include "syl5ib.mm"
include "imp.mm"
include "dmmulpi.mm"
include "0npi.mm"
include "ndmovrcl.mm"
include "simpr.mm"
include "3syl.mm"
include "comu.mm"
include "mulpiord.mm"
include "adantr.mm"
include "adantlr.mm"
include "eqeq12d.mm"
include "com.mm"
include "pinn.mm"
include "w3a.mm"
include "c0.mm"
include "elni2.mm"
include "simprbi.mm"
include "nnmcan.mm"
include "biimpd.mm"
include "sylan2.mm"
include "ex.mm"
include "syl3an.mm"
include "3exp.mm"
include "com4r.mm"
include "pm2.43i.mm"
include "imp31.mm"
include "sylbid.mm"
include "exp32.mm"
include "imp4b.mm"
include "oveq2.mm"
include "impbid1.mm"

theorem mulcanpi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. N. /\ B e. N. ) -> ( ( A .N B ) = ( A .N C ) <-> B = C ) )

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
    cmi
    co
    #
    cA
    cC
    cmi
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
    mulclpi
    @3
    @4
    cnpi
    eleq1
    syl5ib
    imp
    cA
    cC
    cnpi
    cmi
    dmmulpi
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
    comu
    co
    #
    cA
    cC
    comu
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
    mulpiord
    adantr
    @0
    @9
    @4
    @13
    wceq
    @1
    cA
    cC
    mulpiord
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
    @1
    @9
    @15
    wi
    wi
    @0
    @1
    @9
    @0
    @15
    @0
    @1
    @9
    @0
    @15
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
    @16
    cA
    pinn
    cB
    pinn
    cC
    pinn
    @17
    @18
    @19
    w3a
    #
    @0
    @15
    @0
    @20
    c0
    cA
    wcel
    #
    @15
    @0
    @17
    @21
    cA
    elni2
    simprbi
    @20
    @21
    wa
    @14
    @6
    cA
    cB
    cC
    nnmcan
    biimpd
    sylan2
    ex
    syl3an
    3exp
    com4r
    pm2.43i
    imp31
    sylbid
    sylan2
    exp32
    imp4b
    pm2.43i
    ex
    cB
    cC
    cA
    cmi
    oveq2
    impbid1
end
