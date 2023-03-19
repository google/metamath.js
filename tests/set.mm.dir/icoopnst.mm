include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cioc.mm"
include "co.mm"
include "cico.mm"
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
include "cmin.mm"
include "iooretop.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "w3a.mm"
include "wi.mm"
include "simp1.mm"
include "a1i.mm"
include "ltm1.mm"
include "adantr.mm"
include "peano2rem.mm"
include "ltletr.mm"
include "3expb.mm"
include "mpancom.mm"
include "mpand.mm"
include "impr.mm"
include "3adantr3.mm"
include "ex.mm"
include "ad2antrr.mm"
include "simp3.mm"
include "3jcad.mm"
include "simp2.mm"
include "cxr.mm"
include "wb.mm"
include "rexr.mm"
include "elioc2.mm"
include "sylan.mm"
include "biimpa.mm"
include "ltleletr.mm"
include "3expa.mm"
include "an31s.mm"
include "imp.mm"
include "ancom2s.mm"
include "an4s.mm"
include "3adantr2.mm"
include "anasss.mm"
include "adantll.mm"
include "syldan.mm"
include "jcad.mm"
include "simpl1.mm"
include "simpr2.mm"
include "simpl3.mm"
include "3jca.mm"
include "impbid1.mm"
include "simpll.mm"
include "simp1d.mm"
include "rexrd.mm"
include "elico2.mm"
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
include "syl.mm"
include "eleqtrrd.mm"

theorem icoopnst
  let cA: class A
  let cB: class B
  let cC: class C
  let cJ: class J
  let vv: setvar v
  assume icoopnst.1: |- J = ( MetOpen ` ( ( abs o. - ) |` ( ( A [,] B ) X. ( A [,] B ) ) ) )


  assert |- ( ( A e. RR /\ B e. RR ) -> ( C e. ( A (,] B ) -> ( A [,) C ) e. J ) )

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
    cioc
    co
    wcel
    #
    cA
    cC
    cico
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
    cA
    c1
    cmin
    co
    #
    cC
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
    @14
    cC
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
    cA
    @9
    cle
    wbr
    #
    @9
    cC
    clt
    wbr
    #
    w3a
    #
    @18
    @14
    @9
    clt
    wbr
    #
    @20
    w3a
    #
    @18
    @19
    @9
    cB
    cle
    wbr
    #
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
    @22
    @20
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
    @0
    @21
    @22
    wi
    @1
    @3
    @0
    @21
    @22
    @0
    @18
    @19
    @22
    @20
    @0
    @18
    @19
    @22
    @0
    @18
    wa
    #
    @14
    cA
    clt
    wbr
    #
    @19
    @22
    @0
    @31
    @18
    cA
    ltm1
    adantr
    @14
    cr
    wcel
    #
    @30
    @31
    @19
    wa
    @22
    wi
    #
    @0
    @32
    @18
    cA
    peano2rem
    #
    adantr
    @32
    @0
    @18
    @33
    @14
    cA
    @9
    ltletr
    3expb
    mpancom
    mpand
    impr
    3adantr3
    ex
    ad2antrr
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
    @5
    @21
    @18
    @19
    @24
    @29
    @21
    @19
    wi
    @5
    @18
    @19
    @20
    simp2
    a1i
    @2
    @3
    cC
    cr
    wcel
    #
    cA
    cC
    clt
    wbr
    #
    cC
    cB
    cle
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
    @0
    cA
    cxr
    wcel
    @1
    @3
    @38
    wb
    cA
    rexr
    cA
    cB
    cC
    elioc2
    sylan
    biimpa
    #
    @1
    @38
    @39
    @0
    @1
    @35
    @37
    @39
    @36
    @1
    @35
    @37
    @39
    @1
    @35
    wa
    #
    @37
    wa
    #
    @21
    @24
    @42
    @18
    @20
    @24
    @19
    @41
    @18
    @37
    @20
    @24
    @41
    @18
    wa
    #
    @20
    @37
    @24
    @43
    @20
    @37
    wa
    #
    @24
    @18
    @35
    @1
    @44
    @24
    wi
    #
    @18
    @35
    @1
    @45
    @9
    cC
    cB
    ltleletr
    3expa
    an31s
    imp
    ancom2s
    an4s
    3adantr2
    ex
    anasss
    3adantr2
    adantll
    syldan
    3jcad
    jcad
    @26
    @18
    @19
    @20
    @18
    @22
    @20
    @25
    simpl1
    @23
    @18
    @19
    @24
    simpr2
    @18
    @22
    @20
    @25
    simpl3
    3jca
    impbid1
    @5
    @0
    cC
    cxr
    wcel
    #
    @27
    @21
    wb
    @0
    @1
    @3
    simpll
    @5
    cC
    @5
    @35
    @36
    @37
    @40
    simp1d
    rexrd
    #
    cA
    cC
    @9
    elico2
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
    @48
    @23
    @49
    @25
    @5
    @14
    cxr
    wcel
    #
    @46
    @48
    @23
    wb
    @0
    @50
    @1
    @3
    @0
    @14
    @34
    rexrd
    ad2antrr
    @47
    @14
    cC
    @9
    elioo2
    syl2anc
    @2
    @49
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
    @51
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
    icoopnst.1
    resubmet
    syl
    eleqtrrd
    ex
end
