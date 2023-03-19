include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "cxmu.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "xmulgt0.mm"
include "an4s.mm"
include "0xr.mm"
include "xmulcl.mm"
include "adantr.mm"
include "xrltle.mm"
include "sylancr.mm"
include "mpd.mm"
include "ex.mm"
include "ad2ant2r.mm"
include "impl.mm"
include "0le0.mm"
include "oveq2.mm"
include "eqcomd.mm"
include "xmul01.mm"
include "ad2antrr.mm"
include "sylan9eqr.mm"
include "syl5breqr.mm"
include "adantlr.mm"
include "wo.mm"
include "wb.mm"
include "xrleloe.mm"
include "mpan.mm"
include "biimpa.mm"
include "ad2antlr.mm"
include "mpjaodan.mm"
include "oveq1.mm"
include "xmul02.mm"
include "ad2antrl.mm"

theorem xmulge0
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR* /\ 0 <_ A ) /\ ( B e. RR* /\ 0 <_ B ) ) -> 0 <_ ( A *e B ) )

  proof
    cA
    cxr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cB
    cxr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    wa
    #
    cc0
    cA
    clt
    wbr
    #
    cc0
    cA
    cB
    cxmu
    co
    #
    cle
    wbr
    #
    cc0
    cA
    wceq
    #
    @6
    @7
    wa
    cc0
    cB
    clt
    wbr
    #
    @9
    cc0
    cB
    wceq
    #
    @6
    @7
    @11
    @9
    @0
    @3
    @7
    @11
    wa
    #
    @9
    wi
    @1
    @4
    @0
    @3
    wa
    #
    @13
    @9
    @14
    @13
    wa
    #
    cc0
    @8
    clt
    wbr
    #
    @9
    @0
    @7
    @3
    @11
    @16
    cA
    cB
    xmulgt0
    an4s
    @15
    cc0
    cxr
    wcel
    #
    @8
    cxr
    wcel
    #
    @16
    @9
    wi
    0xr
    @14
    @18
    @13
    cA
    cB
    xmulcl
    adantr
    cc0
    @8
    xrltle
    sylancr
    mpd
    ex
    ad2ant2r
    impl
    @6
    @12
    @9
    @7
    @6
    @12
    wa
    cc0
    cc0
    @8
    cle
    0le0
    @12
    @6
    @8
    cA
    cc0
    cxmu
    co
    #
    cc0
    @12
    @19
    @8
    cc0
    cB
    cA
    cxmu
    oveq2
    eqcomd
    @0
    @19
    cc0
    wceq
    @1
    @5
    cA
    xmul01
    ad2antrr
    sylan9eqr
    syl5breqr
    adantlr
    @5
    @11
    @12
    wo
    #
    @2
    @7
    @3
    @4
    @20
    @17
    @3
    @4
    @20
    wb
    0xr
    cc0
    cB
    xrleloe
    mpan
    biimpa
    ad2antlr
    mpjaodan
    @6
    @10
    wa
    cc0
    cc0
    @8
    cle
    0le0
    @10
    @6
    @8
    cc0
    cB
    cxmu
    co
    #
    cc0
    @10
    @21
    @8
    cc0
    cA
    cB
    cxmu
    oveq1
    eqcomd
    @3
    @21
    cc0
    wceq
    @2
    @4
    cB
    xmul02
    ad2antrl
    sylan9eqr
    syl5breqr
    @2
    @7
    @10
    wo
    #
    @5
    @0
    @1
    @22
    @17
    @0
    @1
    @22
    wb
    0xr
    cc0
    cA
    xrleloe
    mpan
    biimpa
    adantr
    mpjaodan
end
