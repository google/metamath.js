include "cxr.mm"
include "wcel.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "cxne.mm"
include "cxad.mm"
include "co.mm"
include "cr.mm"
include "wa.mm"
include "wi.mm"
include "w3a.mm"
include "necom.mm"
include "clt.mm"
include "xrleltne.mm"
include "cmnf.mm"
include "mnfxr.mm"
include "a1i.mm"
include "simpl1.mm"
include "simpl2.mm"
include "cpnf.mm"
include "pnfnre.mm"
include "neli.mm"
include "wceq.mm"
include "mnfle.mm"
include "syl.mm"
include "simpl3.mm"
include "xrlelttrd.mm"
include "xrltne.mm"
include "syl3anc.mm"
include "xaddpnf1.mm"
include "syl2anc.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "wn.mm"
include "wb.mm"
include "ngtmnft.mm"
include "simpr.mm"
include "xnegeq.mm"
include "xnegmnf.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "syl5ibcom.mm"
include "sylbird.mm"
include "mt3d.mm"
include "xrre2.mm"
include "syl32anc.mm"
include "pnfxr.mm"
include "xnegcld.mm"
include "xnegpnf.mm"
include "pnfge.mm"
include "xrltletrd.mm"
include "xltnegi.mm"
include "syl5eqbrr.mm"
include "xaddpnf2.mm"
include "nltpnft.mm"
include "oveq1.mm"
include "jca.mm"
include "ex.mm"
include "3expia.mm"
include "3adant3.mm"
include "syl5bi.mm"
include "3exp.mm"
include "com34.mm"
include "3imp1.mm"

theorem xrsdsreclblem
  let cA: class A
  let cB: class B
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  assume xrsds.d: |- D = ( dist ` RR*s )


  assert |- ( ( ( A e. RR* /\ B e. RR* /\ A =/= B ) /\ A <_ B ) -> ( ( B +e -e A ) e. RR -> ( A e. RR /\ B e. RR ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    wne
    #
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    cxne
    #
    cxad
    co
    #
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    wi
    #
    @0
    @1
    @3
    @2
    @10
    @0
    @1
    @3
    @2
    @10
    wi
    @2
    cB
    cA
    wne
    #
    @0
    @1
    @3
    w3a
    #
    @10
    cA
    cB
    necom
    @12
    @11
    cA
    cB
    clt
    wbr
    #
    @10
    cA
    cB
    xrleltne
    @0
    @1
    @13
    @10
    wi
    @3
    @0
    @1
    @13
    @10
    @0
    @1
    @13
    w3a
    #
    @6
    @9
    @14
    @6
    wa
    #
    @7
    @8
    @15
    cmnf
    cxr
    wcel
    #
    @0
    @1
    cmnf
    cA
    clt
    wbr
    #
    @13
    @7
    @16
    @15
    mnfxr
    a1i
    #
    @0
    @1
    @13
    @6
    simpl1
    #
    @0
    @1
    @13
    @6
    simpl2
    #
    @15
    @17
    cB
    cpnf
    cxad
    co
    #
    cr
    wcel
    #
    @15
    @22
    cpnf
    cr
    wcel
    #
    cpnf
    cr
    pnfnre
    neli
    #
    @15
    @21
    cpnf
    cr
    @15
    @1
    cB
    cmnf
    wne
    #
    @21
    cpnf
    wceq
    @20
    @15
    @16
    @1
    cmnf
    cB
    clt
    wbr
    @25
    @18
    @20
    @15
    cmnf
    cA
    cB
    @18
    @19
    @20
    @15
    @0
    cmnf
    cA
    cle
    wbr
    @19
    cA
    mnfle
    syl
    @0
    @1
    @13
    @6
    simpl3
    #
    xrlelttrd
    cmnf
    cB
    xrltne
    syl3anc
    cB
    xaddpnf1
    syl2anc
    eleq1d
    mtbiri
    @15
    @17
    wn
    #
    cA
    cmnf
    wceq
    #
    @22
    @15
    @0
    @28
    @27
    wb
    @19
    cA
    ngtmnft
    syl
    @15
    @6
    @28
    @22
    @14
    @6
    simpr
    #
    @28
    @5
    @21
    cr
    @28
    @4
    cpnf
    cB
    cxad
    @28
    @4
    cmnf
    cxne
    cpnf
    cA
    cmnf
    xnegeq
    xnegmnf
    syl6eq
    oveq2d
    eleq1d
    syl5ibcom
    sylbird
    mt3d
    @26
    cmnf
    cA
    cB
    xrre2
    syl32anc
    @15
    @0
    @1
    cpnf
    cxr
    wcel
    #
    @13
    cB
    cpnf
    clt
    wbr
    #
    @8
    @19
    @20
    @30
    @15
    pnfxr
    a1i
    #
    @26
    @15
    @31
    cpnf
    @4
    cxad
    co
    #
    cr
    wcel
    #
    @15
    @34
    @23
    @24
    @15
    @33
    cpnf
    cr
    @15
    @4
    cxr
    wcel
    #
    @4
    cmnf
    wne
    #
    @33
    cpnf
    wceq
    @15
    cA
    @19
    xnegcld
    #
    @15
    @16
    @35
    cmnf
    @4
    clt
    wbr
    @36
    @18
    @37
    @15
    cmnf
    cpnf
    cxne
    #
    @4
    clt
    xnegpnf
    @15
    @0
    @30
    cA
    cpnf
    clt
    wbr
    @38
    @4
    clt
    wbr
    @19
    @32
    @15
    cA
    cB
    cpnf
    @19
    @20
    @32
    @26
    @15
    @1
    cB
    cpnf
    cle
    wbr
    @20
    cB
    pnfge
    syl
    xrltletrd
    cA
    cpnf
    xltnegi
    syl3anc
    syl5eqbrr
    cmnf
    @4
    xrltne
    syl3anc
    @4
    xaddpnf2
    syl2anc
    eleq1d
    mtbiri
    @15
    @31
    wn
    #
    cB
    cpnf
    wceq
    #
    @34
    @15
    @1
    @40
    @39
    wb
    @20
    cB
    nltpnft
    syl
    @15
    @6
    @40
    @34
    @29
    @40
    @5
    @33
    cr
    cB
    cpnf
    @4
    cxad
    oveq1
    eleq1d
    syl5ibcom
    sylbird
    mt3d
    cA
    cB
    cpnf
    xrre2
    syl32anc
    jca
    ex
    3expia
    3adant3
    sylbird
    syl5bi
    3exp
    com34
    3imp1
end
