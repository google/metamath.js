include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cico.mm"
include "co.mm"
include "cioc.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cicc.mm"
include "crest.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "c1.mm"
include "caddc.mm"
include "iooretop.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "w3a.mm"
include "wi.mm"
include "simp1.mm"
include "a1i.mm"
include "simp2.mm"
include "ltp1.mm"
include "adantr.mm"
include "peano2re.mm"
include "lelttr.mm"
include "3expa.mm"
include "ancom1s.mm"
include "ancomsd.mm"
include "mpidan.mm"
include "mpand.mm"
include "impr.mm"
include "3adantr2.mm"
include "ex.mm"
include "ad2antlr.mm"
include "3jcad.mm"
include "cxr.mm"
include "wb.mm"
include "rexr.mm"
include "elico2.mm"
include "sylan2.mm"
include "biimpa.mm"
include "ltle.mm"
include "3adant2.mm"
include "syld.mm"
include "imp.mm"
include "an4s.mm"
include "3adantr3.mm"
include "anasss.mm"
include "adantlr.mm"
include "syldan.mm"
include "simp3.mm"
include "jcad.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr3.mm"
include "3jca.mm"
include "impbid1.mm"
include "simp1d.mm"
include "syl.mm"
include "simplr.mm"
include "elioc2.mm"
include "syl2anc.mm"
include "elin.mm"
include "elioo2.mm"
include "elicc2.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "3bitr4d.mm"
include "eqrdv.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylancr.mm"
include "ctop.mm"
include "cvv.mm"
include "retop.mm"
include "ovex.mm"
include "elrest.mm"
include "mp2an.mm"
include "sylibr.mm"
include "wss.mm"
include "iccssre.mm"
include "eqid.mm"
include "resubmet.mm"
include "eleqtrrd.mm"

theorem iocopnst
  let cA: class A
  let cB: class B
  let cC: class C
  let cJ: class J
  let vv: setvar v
  assume iocopnst.1: |- J = ( MetOpen ` ( ( abs o. - ) |` ( ( A [,] B ) X. ( A [,] B ) ) ) )


  assert |- ( ( A e. RR /\ B e. RR ) -> ( C e. ( A [,) B ) -> ( C (,] B ) e. J ) )

  proof
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
    cC
    cA
    cB
    cico
    co
    wcel
    #
    cC
    cB
    cioc
    co
    #
    cJ
    wcel
    @2
    @3
    wa
    #
    @4
    cioo
    crn
    ctg
    cfv
    #
    cA
    cB
    cicc
    co
    #
    crest
    co
    #
    cJ
    @5
    @4
    vv
    cv
    #
    @7
    cin
    #
    wceq
    #
    vv
    @6
    wrex
    #
    @4
    @8
    wcel
    #
    @5
    cC
    cB
    c1
    caddc
    co
    #
    cioo
    co
    #
    @6
    wcel
    @4
    @15
    @7
    cin
    #
    wceq
    #
    @12
    cC
    @14
    iooretop
    @5
    vv
    @4
    @16
    @5
    @9
    cr
    wcel
    #
    cC
    @9
    clt
    wbr
    #
    @9
    cB
    cle
    wbr
    #
    w3a
    #
    @18
    @19
    @9
    @14
    clt
    wbr
    #
    w3a
    #
    @18
    cA
    @9
    cle
    wbr
    #
    @20
    w3a
    #
    wa
    #
    @9
    @4
    wcel
    #
    @9
    @16
    wcel
    #
    @5
    @21
    @26
    @5
    @21
    @23
    @25
    @5
    @21
    @18
    @19
    @22
    @21
    @18
    wi
    @5
    @18
    @19
    @20
    simp1
    a1i
    #
    @21
    @19
    wi
    @5
    @18
    @19
    @20
    simp2
    a1i
    @1
    @21
    @22
    wi
    @0
    @3
    @1
    @21
    @22
    @1
    @18
    @20
    @22
    @19
    @1
    @18
    @20
    @22
    @1
    @18
    wa
    #
    cB
    @14
    clt
    wbr
    #
    @20
    @22
    @1
    @31
    @18
    cB
    ltp1
    adantr
    @1
    @18
    @14
    cr
    wcel
    #
    @31
    @20
    wa
    @22
    wi
    cB
    peano2re
    #
    @30
    @32
    wa
    @20
    @31
    @22
    @18
    @1
    @32
    @20
    @31
    wa
    @22
    wi
    #
    @18
    @1
    @32
    @34
    @9
    cB
    @14
    lelttr
    3expa
    ancom1s
    ancomsd
    mpidan
    mpand
    impr
    3adantr2
    ex
    ad2antlr
    3jcad
    @5
    @21
    @18
    @24
    @20
    @29
    @2
    @3
    cC
    cr
    wcel
    #
    cA
    cC
    cle
    wbr
    #
    cC
    cB
    clt
    wbr
    #
    w3a
    #
    @21
    @24
    wi
    #
    @2
    @3
    @38
    @1
    @0
    cB
    cxr
    wcel
    @3
    @38
    wb
    cB
    rexr
    cA
    cB
    cC
    elico2
    sylan2
    biimpa
    #
    @0
    @38
    @39
    @1
    @0
    @35
    @36
    @39
    @37
    @0
    @35
    @36
    @39
    @0
    @35
    wa
    #
    @36
    wa
    #
    @21
    @24
    @42
    @18
    @19
    @24
    @20
    @41
    @18
    @36
    @19
    @24
    @41
    @18
    wa
    @36
    @19
    wa
    #
    @24
    @0
    @35
    @18
    @43
    @24
    wi
    @0
    @35
    @18
    w3a
    @43
    cA
    @9
    clt
    wbr
    #
    @24
    cA
    cC
    @9
    lelttr
    @0
    @18
    @44
    @24
    wi
    @35
    cA
    @9
    ltle
    3adant2
    syld
    3expa
    imp
    an4s
    3adantr3
    ex
    anasss
    3adantr3
    adantlr
    syldan
    @21
    @20
    wi
    @5
    @18
    @19
    @20
    simp3
    a1i
    3jcad
    jcad
    @26
    @18
    @19
    @20
    @18
    @19
    @22
    @25
    simpl1
    @18
    @19
    @22
    @25
    simpl2
    @23
    @18
    @24
    @20
    simpr3
    3jca
    impbid1
    @5
    cC
    cxr
    wcel
    #
    @1
    @27
    @21
    wb
    @5
    @35
    @45
    @5
    @35
    @36
    @37
    @40
    simp1d
    cC
    rexr
    syl
    #
    @0
    @1
    @3
    simplr
    cC
    cB
    @9
    elioc2
    syl2anc
    @28
    @9
    @15
    wcel
    #
    @9
    @7
    wcel
    #
    wa
    @5
    @26
    @9
    @15
    @7
    elin
    @5
    @47
    @23
    @48
    @25
    @5
    @45
    @14
    cxr
    wcel
    #
    @47
    @23
    wb
    @46
    @1
    @49
    @0
    @3
    @1
    @32
    @49
    @33
    @14
    rexr
    syl
    ad2antlr
    cC
    @14
    @9
    elioo2
    syl2anc
    @2
    @48
    @25
    wb
    @3
    cA
    cB
    @9
    elicc2
    adantr
    anbi12d
    syl5bb
    3bitr4d
    eqrdv
    @11
    @17
    vv
    @15
    @6
    @9
    @15
    wceq
    @10
    @16
    @4
    @9
    @15
    @7
    ineq1
    eqeq2d
    rspcev
    sylancr
    @6
    ctop
    wcel
    @7
    cvv
    wcel
    @13
    @12
    wb
    retop
    cA
    cB
    cicc
    ovex
    vv
    @4
    @7
    @6
    ctop
    cvv
    elrest
    mp2an
    sylibr
    @5
    @7
    cr
    wss
    #
    cJ
    @8
    wceq
    @2
    @50
    @3
    cA
    cB
    iccssre
    adantr
    @7
    @6
    cJ
    @6
    eqid
    iocopnst.1
    resubmet
    syl
    eleqtrrd
    ex
end
