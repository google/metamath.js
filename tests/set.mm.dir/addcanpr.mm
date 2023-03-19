include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "cpp.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "addclpr.mm"
include "eleq1.mm"
include "dmplp.mm"
include "0npr.mm"
include "ndmovrcl.mm"
include "syl6bi.mm"
include "syl5com.mm"
include "cltp.mm"
include "wbr.mm"
include "wo.mm"
include "wn.mm"
include "wb.mm"
include "ltapr.mm"
include "orbi12d.mm"
include "notbid.mm"
include "ad2antrr.mm"
include "wor.mm"
include "ltsopr.mm"
include "sotrieq.mm"
include "mpan.mm"
include "ad2ant2l.mm"
include "syl2an.mm"
include "3bitr4d.mm"
include "exbiri.mm"
include "syld.mm"
include "pm2.43d.mm"

theorem addcanpr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. P. /\ B e. P. ) -> ( ( A +P. B ) = ( A +P. C ) -> B = C ) )

  proof
    cA
    cnp
    wcel
    #
    cB
    cnp
    wcel
    #
    wa
    #
    cA
    cB
    cpp
    co
    #
    cA
    cC
    cpp
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
    @0
    cC
    cnp
    wcel
    #
    wa
    #
    @5
    @6
    wi
    @2
    @3
    cnp
    wcel
    #
    @5
    @8
    cA
    cB
    addclpr
    #
    @5
    @9
    @4
    cnp
    wcel
    #
    @8
    @3
    @4
    cnp
    eleq1
    cA
    cC
    cnp
    cpp
    dmplp
    0npr
    ndmovrcl
    syl6bi
    syl5com
    @2
    @8
    @6
    @5
    @2
    @8
    wa
    cB
    cC
    cltp
    wbr
    #
    cC
    cB
    cltp
    wbr
    #
    wo
    #
    wn
    #
    @3
    @4
    cltp
    wbr
    #
    @4
    @3
    cltp
    wbr
    #
    wo
    #
    wn
    #
    @6
    @5
    @0
    @15
    @19
    wb
    @1
    @8
    @0
    @14
    @18
    @0
    @12
    @16
    @13
    @17
    cB
    cC
    cA
    ltapr
    cC
    cB
    cA
    ltapr
    orbi12d
    notbid
    ad2antrr
    @1
    @7
    @6
    @15
    wb
    #
    @0
    @0
    cnp
    cltp
    wor
    #
    @1
    @7
    wa
    @20
    ltsopr
    cnp
    cB
    cC
    cltp
    sotrieq
    mpan
    ad2ant2l
    @2
    @9
    @11
    @5
    @19
    wb
    #
    @8
    @10
    cA
    cC
    addclpr
    @21
    @9
    @11
    wa
    @22
    ltsopr
    cnp
    @3
    @4
    cltp
    sotrieq
    mpan
    syl2an
    3bitr4d
    exbiri
    syld
    pm2.43d
end
