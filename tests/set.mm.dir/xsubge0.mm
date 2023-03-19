include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "w3o.mm"
include "cc0.mm"
include "cxne.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "elxr.mm"
include "wa.mm"
include "0xr.mm"
include "a1i.mm"
include "rexr.mm"
include "xnegcl.mm"
include "xaddcl.mm"
include "sylan2.mm"
include "simpr.mm"
include "xleadd1.mm"
include "syl3anc.mm"
include "adantl.mm"
include "xaddid2.mm"
include "syl.mm"
include "xnpcan.mm"
include "breq12d.mm"
include "bitrd.mm"
include "pnfxr.mm"
include "xrletri3.mm"
include "mpan2.mm"
include "wne.mm"
include "wn.mm"
include "clt.mm"
include "mnflt0.mm"
include "mnfxr.mm"
include "xrltnle.mm"
include "mp2an.mm"
include "mpbi.mm"
include "xaddmnf1.mm"
include "breq2d.mm"
include "mtbiri.mm"
include "ex.mm"
include "necon4ad.mm"
include "0le0.mm"
include "oveq1.mm"
include "pnfaddmnf.mm"
include "syl6eq.mm"
include "syl5breqr.mm"
include "impbid1.mm"
include "pnfge.mm"
include "biantrurd.mm"
include "3bitr4d.mm"
include "adantr.mm"
include "xnegeq.mm"
include "xnegpnf.mm"
include "oveq2d.mm"
include "breq1.mm"
include "mnfaddpnf.mm"
include "0lepnf.mm"
include "xaddpnf1.mm"
include "pm2.61dane.mm"
include "mnfle.mm"
include "2thd.mm"
include "xnegmnf.mm"
include "3jaodan.mm"
include "sylan2b.mm"

theorem xsubge0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( 0 <_ ( A +e -e B ) <-> B <_ A ) )

  proof
    cB
    cxr
    wcel
    #
    cA
    cxr
    wcel
    #
    cB
    cr
    wcel
    #
    cB
    cpnf
    wceq
    #
    cB
    cmnf
    wceq
    #
    w3o
    cc0
    cA
    cB
    cxne
    #
    cxad
    co
    #
    cle
    wbr
    #
    cB
    cA
    cle
    wbr
    #
    wb
    #
    cB
    elxr
    @1
    @2
    @9
    @3
    @4
    @1
    @2
    wa
    #
    @7
    cc0
    cB
    cxad
    co
    #
    @6
    cB
    cxad
    co
    #
    cle
    wbr
    #
    @8
    @10
    cc0
    cxr
    wcel
    #
    @6
    cxr
    wcel
    #
    @2
    @7
    @13
    wb
    @14
    @10
    0xr
    a1i
    @2
    @1
    @0
    @15
    cB
    rexr
    #
    @0
    @1
    @5
    cxr
    wcel
    @15
    cB
    xnegcl
    cA
    @5
    xaddcl
    sylan2
    sylan2
    @1
    @2
    simpr
    cc0
    @6
    cB
    xleadd1
    syl3anc
    @10
    @11
    cB
    @12
    cA
    cle
    @10
    @0
    @11
    cB
    wceq
    @2
    @0
    @1
    @16
    adantl
    cB
    xaddid2
    syl
    cA
    cB
    xnpcan
    breq12d
    bitrd
    @1
    @3
    wa
    #
    cc0
    cA
    cmnf
    cxad
    co
    #
    cle
    wbr
    #
    cpnf
    cA
    cle
    wbr
    #
    @7
    @8
    @1
    @19
    @20
    wb
    @3
    @1
    cA
    cpnf
    wceq
    #
    cA
    cpnf
    cle
    wbr
    #
    @20
    wa
    #
    @19
    @20
    @1
    cpnf
    cxr
    wcel
    @21
    @23
    wb
    pnfxr
    cA
    cpnf
    xrletri3
    mpan2
    @1
    @19
    @21
    @1
    @19
    cA
    cpnf
    @1
    cA
    cpnf
    wne
    #
    @19
    wn
    @1
    @24
    wa
    #
    @19
    cc0
    cmnf
    cle
    wbr
    #
    cmnf
    cc0
    clt
    wbr
    #
    @26
    wn
    #
    mnflt0
    cmnf
    cxr
    wcel
    @14
    @27
    @28
    wb
    mnfxr
    0xr
    cmnf
    cc0
    xrltnle
    mp2an
    mpbi
    @25
    @18
    cmnf
    cc0
    cle
    cA
    xaddmnf1
    breq2d
    mtbiri
    ex
    necon4ad
    @21
    cc0
    cc0
    @18
    cle
    0le0
    @21
    @18
    cpnf
    cmnf
    cxad
    co
    cc0
    cA
    cpnf
    cmnf
    cxad
    oveq1
    pnfaddmnf
    syl6eq
    syl5breqr
    impbid1
    @1
    @22
    @20
    cA
    pnfge
    biantrurd
    3bitr4d
    adantr
    @17
    @6
    @18
    cc0
    cle
    @17
    @5
    cmnf
    cA
    cxad
    @3
    @5
    cmnf
    wceq
    @1
    @3
    @5
    cpnf
    cxne
    cmnf
    cB
    cpnf
    xnegeq
    xnegpnf
    syl6eq
    adantl
    oveq2d
    breq2d
    @3
    @8
    @20
    wb
    @1
    cB
    cpnf
    cA
    cle
    breq1
    adantl
    3bitr4d
    @1
    @4
    wa
    #
    cc0
    cA
    cpnf
    cxad
    co
    #
    cle
    wbr
    #
    cmnf
    cA
    cle
    wbr
    #
    @7
    @8
    @1
    @31
    @32
    wb
    @4
    @1
    @31
    @32
    @1
    @31
    cA
    cmnf
    @1
    cA
    cmnf
    wceq
    #
    wa
    cc0
    cc0
    @30
    cle
    0le0
    @33
    @30
    cc0
    wceq
    @1
    @33
    @30
    cmnf
    cpnf
    cxad
    co
    cc0
    cA
    cmnf
    cpnf
    cxad
    oveq1
    mnfaddpnf
    syl6eq
    adantl
    syl5breqr
    @1
    cA
    cmnf
    wne
    wa
    cc0
    cpnf
    @30
    cle
    0lepnf
    cA
    xaddpnf1
    syl5breqr
    pm2.61dane
    cA
    mnfle
    2thd
    adantr
    @29
    @6
    @30
    cc0
    cle
    @29
    @5
    cpnf
    cA
    cxad
    @4
    @5
    cpnf
    wceq
    @1
    @4
    @5
    cmnf
    cxne
    cpnf
    cB
    cmnf
    xnegeq
    xnegmnf
    syl6eq
    adantl
    oveq2d
    breq2d
    @4
    @8
    @32
    wb
    @1
    cB
    cmnf
    cA
    cle
    breq1
    adantl
    3bitr4d
    3jaodan
    sylan2b
end
