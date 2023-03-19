include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "w3o.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "elxr.mm"
include "ltnsym.mm"
include "wa.mm"
include "rexr.mm"
include "pnfnlt.mm"
include "syl.mm"
include "adantr.mm"
include "wb.mm"
include "breq1.mm"
include "adantl.mm"
include "mtbird.mm"
include "a1d.mm"
include "nltmnf.mm"
include "breq2.mm"
include "pm2.21d.mm"
include "3jaodan.mm"
include "sylan2br.mm"
include "mnfxr.mm"
include "ax-mp.mm"
include "breq12.mm"
include "mtbiri.mm"
include "ancoms.mm"
include "xrltnr.mm"
include "3jaoian.mm"
include "syl2anb.mm"

theorem xrltnsym
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A < B -> -. B < A ) )

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
    #
    cA
    cB
    clt
    wbr
    #
    cB
    cA
    clt
    wbr
    #
    wn
    #
    wi
    #
    cB
    cxr
    wcel
    #
    cA
    elxr
    cB
    elxr
    #
    @1
    @7
    @11
    @2
    @3
    @1
    @4
    @11
    @5
    @6
    cA
    cB
    ltnsym
    @1
    @5
    wa
    #
    @10
    @8
    @14
    @9
    cpnf
    cA
    clt
    wbr
    #
    @1
    @15
    wn
    #
    @5
    @1
    @0
    @16
    cA
    rexr
    #
    cA
    pnfnlt
    syl
    adantr
    @5
    @9
    @15
    wb
    @1
    cB
    cpnf
    cA
    clt
    breq1
    adantl
    mtbird
    a1d
    @1
    @6
    wa
    #
    @8
    @10
    @18
    @8
    cA
    cmnf
    clt
    wbr
    #
    @1
    @19
    wn
    #
    @6
    @1
    @0
    @20
    @17
    cA
    nltmnf
    syl
    adantr
    @6
    @8
    @19
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
    3jaodan
    @7
    @2
    @12
    @11
    @13
    @2
    @12
    wa
    #
    @8
    @10
    @21
    @8
    cpnf
    cB
    clt
    wbr
    #
    @12
    @22
    wn
    @2
    cB
    pnfnlt
    adantl
    @2
    @8
    @22
    wb
    @12
    cA
    cpnf
    cB
    clt
    breq1
    adantr
    mtbird
    pm2.21d
    sylan2br
    @3
    @4
    @11
    @5
    @6
    @3
    @4
    wa
    #
    @10
    @8
    @23
    @9
    cB
    cmnf
    clt
    wbr
    #
    @4
    @24
    wn
    #
    @3
    @4
    @12
    @25
    cB
    rexr
    cB
    nltmnf
    syl
    adantl
    @3
    @9
    @24
    wb
    @4
    cA
    cmnf
    cB
    clt
    breq2
    adantr
    mtbird
    a1d
    @3
    @5
    wa
    @10
    @8
    @5
    @3
    @10
    @5
    @3
    wa
    @9
    cpnf
    cmnf
    clt
    wbr
    #
    cmnf
    cxr
    wcel
    #
    @26
    wn
    mnfxr
    cmnf
    pnfnlt
    ax-mp
    cB
    cpnf
    cA
    cmnf
    clt
    breq12
    mtbiri
    ancoms
    a1d
    @3
    @6
    wa
    #
    @8
    @10
    @28
    @8
    cmnf
    cmnf
    clt
    wbr
    #
    @27
    @29
    wn
    mnfxr
    cmnf
    xrltnr
    ax-mp
    cA
    cmnf
    cB
    cmnf
    clt
    breq12
    mtbiri
    pm2.21d
    3jaodan
    3jaoian
    syl2anb
end
