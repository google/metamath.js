include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "cdvds.mm"
include "wbr.mm"
include "w3a.mm"
include "wa.mm"
include "cpc.mm"
include "co.mm"
include "cle.mm"
include "cc0.mm"
include "wceq.mm"
include "cxr.mm"
include "cq.mm"
include "0z.mm"
include "zq.mm"
include "ax-mp.mm"
include "pcxcl.mm"
include "mpan2.mm"
include "xrleid.mm"
include "syl.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "oveq2d.mm"
include "simplr3.mm"
include "eqbrtrrd.mm"
include "wb.mm"
include "simplr2.mm"
include "0dvds.mm"
include "mpbid.mm"
include "3brtr4d.mm"
include "wne.mm"
include "cexp.mm"
include "simpll.mm"
include "simplr1.mm"
include "pczdvds.mm"
include "syl12anc.mm"
include "wi.mm"
include "cn.mm"
include "prmnn.mm"
include "cn0.mm"
include "pczcl.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "pcdvdsb.mm"
include "mpbird.mm"
include "pm2.61dane.mm"

theorem pcdvdstr
  let cA: class A
  let cB: class B
  let cP: class P


  assert |- ( ( P e. Prime /\ ( A e. ZZ /\ B e. ZZ /\ A || B ) ) -> ( P pCnt A ) <_ ( P pCnt B ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cA
    cB
    cdvds
    wbr
    #
    w3a
    #
    wa
    #
    cP
    cA
    cpc
    co
    #
    cP
    cB
    cpc
    co
    #
    cle
    wbr
    #
    cA
    cc0
    @5
    cA
    cc0
    wceq
    #
    wa
    #
    cP
    cc0
    cpc
    co
    #
    @11
    @6
    @7
    cle
    @0
    @11
    @11
    cle
    wbr
    #
    @4
    @9
    @0
    @11
    cxr
    wcel
    #
    @12
    @0
    cc0
    cq
    wcel
    #
    @13
    cc0
    cz
    wcel
    @14
    0z
    cc0
    zq
    ax-mp
    cP
    cc0
    pcxcl
    mpan2
    @11
    xrleid
    syl
    ad2antrr
    @10
    cA
    cc0
    cP
    cpc
    @5
    @9
    simpr
    #
    oveq2d
    @10
    cB
    cc0
    cP
    cpc
    @10
    cc0
    cB
    cdvds
    wbr
    #
    cB
    cc0
    wceq
    #
    @10
    cA
    cc0
    cB
    cdvds
    @15
    @1
    @2
    @3
    @0
    @9
    simplr3
    eqbrtrrd
    @10
    @2
    @16
    @17
    wb
    @1
    @2
    @3
    @0
    @9
    simplr2
    cB
    0dvds
    syl
    mpbid
    oveq2d
    3brtr4d
    @5
    cA
    cc0
    wne
    #
    wa
    #
    @8
    cP
    @6
    cexp
    co
    #
    cB
    cdvds
    wbr
    #
    @19
    @20
    cA
    cdvds
    wbr
    #
    @3
    @21
    @19
    @0
    @1
    @18
    @22
    @0
    @4
    @18
    simpll
    #
    @1
    @2
    @3
    @0
    @18
    simplr1
    #
    @5
    @18
    simpr
    #
    cP
    cA
    pczdvds
    syl12anc
    @1
    @2
    @3
    @0
    @18
    simplr3
    @19
    @20
    cz
    wcel
    @1
    @2
    @22
    @3
    wa
    @21
    wi
    @19
    @20
    @19
    cP
    @6
    @19
    @0
    cP
    cn
    wcel
    @23
    cP
    prmnn
    syl
    @19
    @0
    @1
    @18
    @6
    cn0
    wcel
    #
    @23
    @24
    @25
    cP
    cA
    pczcl
    syl12anc
    #
    nnexpcld
    nnzd
    @24
    @1
    @2
    @3
    @0
    @18
    simplr2
    #
    @20
    cA
    cB
    dvdstr
    syl3anc
    mp2and
    @19
    @0
    @2
    @26
    @8
    @21
    wb
    @23
    @28
    @27
    @6
    cP
    cB
    pcdvdsb
    syl3anc
    mpbird
    pm2.61dane
end
