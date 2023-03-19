include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "w3o.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "elxr.mm"
include "lttr.mm"
include "3expa.mm"
include "an32s.mm"
include "wn.mm"
include "rexr.mm"
include "pnfnlt.mm"
include "syl.mm"
include "adantr.mm"
include "wb.mm"
include "breq1.mm"
include "adantl.mm"
include "mtbird.mm"
include "pm2.21d.mm"
include "adantll.mm"
include "adantld.mm"
include "nltmnf.mm"
include "breq2.mm"
include "adantlr.mm"
include "adantrd.mm"
include "3jaodan.mm"
include "sylan2b.mm"
include "ltpnf.mm"
include "mpbird.mm"
include "a1d.mm"
include "anasss.mm"
include "adantrr.mm"
include "mnflt.mm"
include "mnfltpnf.mm"
include "breq12.mm"
include "mpbiri.mm"
include "3jaoian.mm"
include "3impb.mm"
include "syl3an3b.mm"
include "syl3an1b.mm"

theorem xrlttr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) -> ( ( A < B /\ B < C ) -> A < C ) )

  proof
    cA
    cxr
    wcel
    #
    cA
    cr
    wcel
    #
    cA
    cpnf
    wceq
    #
    cA
    cmnf
    wceq
    #
    w3o
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    cB
    cC
    clt
    wbr
    #
    wa
    #
    cA
    cC
    clt
    wbr
    #
    wi
    #
    cA
    elxr
    @6
    @4
    @5
    cC
    cr
    wcel
    #
    cC
    cpnf
    wceq
    #
    cC
    cmnf
    wceq
    #
    w3o
    #
    @11
    cC
    elxr
    @4
    @5
    @15
    @11
    @1
    @5
    @15
    wa
    @11
    @2
    @3
    @1
    @5
    @15
    @11
    @1
    @5
    wa
    #
    @12
    @11
    @13
    @14
    @1
    @12
    @5
    @11
    @5
    @1
    @12
    wa
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
    @11
    cB
    elxr
    @17
    @18
    @11
    @19
    @20
    @1
    @18
    @12
    @11
    @1
    @18
    @12
    @11
    cA
    cB
    cC
    lttr
    3expa
    an32s
    @17
    @19
    wa
    @8
    @10
    @7
    @12
    @19
    @8
    @10
    wi
    @1
    @12
    @19
    wa
    #
    @8
    @10
    @21
    @8
    cpnf
    cC
    clt
    wbr
    #
    @12
    @22
    wn
    #
    @19
    @12
    @6
    @23
    cC
    rexr
    cC
    pnfnlt
    syl
    adantr
    @19
    @8
    @22
    wb
    @12
    cB
    cpnf
    cC
    clt
    breq1
    adantl
    mtbird
    pm2.21d
    adantll
    adantld
    @17
    @20
    wa
    @7
    @10
    @8
    @1
    @20
    @7
    @10
    wi
    @12
    @1
    @20
    wa
    #
    @7
    @10
    @24
    @7
    cA
    cmnf
    clt
    wbr
    #
    @1
    @25
    wn
    #
    @20
    @1
    @0
    @26
    cA
    rexr
    cA
    nltmnf
    syl
    adantr
    @20
    @7
    @25
    wb
    @1
    cB
    cmnf
    cA
    clt
    breq2
    adantl
    mtbird
    pm2.21d
    adantlr
    adantrd
    3jaodan
    sylan2b
    an32s
    @16
    @13
    wa
    @10
    @9
    @1
    @13
    @10
    @5
    @1
    @13
    wa
    @10
    cA
    cpnf
    clt
    wbr
    #
    @1
    @27
    @13
    cA
    ltpnf
    adantr
    @13
    @10
    @27
    wb
    @1
    cC
    cpnf
    cA
    clt
    breq2
    adantl
    mpbird
    adantlr
    a1d
    @5
    @14
    @11
    @1
    @5
    @14
    wa
    #
    @8
    @10
    @7
    @28
    @8
    @10
    @28
    @8
    cB
    cmnf
    clt
    wbr
    #
    @5
    @29
    wn
    @14
    cB
    nltmnf
    adantr
    @14
    @8
    @29
    wb
    @5
    cC
    cmnf
    cB
    clt
    breq2
    adantl
    mtbird
    pm2.21d
    adantld
    #
    adantll
    3jaodan
    anasss
    @2
    @5
    @11
    @15
    @2
    @5
    wa
    #
    @7
    @10
    @8
    @31
    @7
    @10
    @31
    @7
    cpnf
    cB
    clt
    wbr
    #
    @5
    @32
    wn
    @2
    cB
    pnfnlt
    adantl
    @2
    @7
    @32
    wb
    @5
    cA
    cpnf
    cB
    clt
    breq1
    adantr
    mtbird
    pm2.21d
    adantrd
    adantrr
    @3
    @5
    @15
    @11
    @3
    @5
    wa
    @12
    @11
    @13
    @14
    @3
    @12
    @11
    @5
    @3
    @12
    wa
    #
    @10
    @9
    @33
    @10
    cmnf
    cC
    clt
    wbr
    #
    @12
    @34
    @3
    cC
    mnflt
    adantl
    @3
    @10
    @34
    wb
    @12
    cA
    cmnf
    cC
    clt
    breq1
    adantr
    mpbird
    a1d
    adantlr
    @3
    @13
    @11
    @5
    @3
    @13
    wa
    #
    @10
    @9
    @35
    @10
    cmnf
    cpnf
    clt
    wbr
    mnfltpnf
    cA
    cmnf
    cC
    cpnf
    clt
    breq12
    mpbiri
    a1d
    adantlr
    @5
    @14
    @11
    @3
    @30
    adantll
    3jaodan
    anasss
    3jaoian
    3impb
    syl3an3b
    syl3an1b
end
