include "cr.mm"
include "wcel.mm"
include "cicc.mm"
include "co.mm"
include "w3a.mm"
include "cun.mm"
include "cv.mm"
include "wo.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "simplr1.mm"
include "simplr2.mm"
include "wi.mm"
include "simpr1.mm"
include "iccssre.mm"
include "sseld.mm"
include "3impia.mm"
include "adantr.mm"
include "ltle.mm"
include "syl2anc.mm"
include "imp.mm"
include "3jca.mm"
include "orcd.mm"
include "simpr.mm"
include "simplr3.mm"
include "olcd.mm"
include "ltlecasei.mm"
include "ex.mm"
include "simp1.mm"
include "a1i.mm"
include "simp2.mm"
include "elicc2.mm"
include "3ad2ant3.mm"
include "3ad2ant2.mm"
include "simp1r.mm"
include "simp3.mm"
include "letrd.mm"
include "3exp.mm"
include "sylbid.mm"
include "3jcad.mm"
include "simp1l.mm"
include "jaod.mm"
include "impbid.mm"
include "wb.mm"
include "3adant3.mm"
include "imdistani.mm"
include "3impa.mm"
include "adantlr.mm"
include "ancoms.mm"
include "adantll.mm"
include "orbi12d.mm"
include "syl.mm"
include "3bitr4d.mm"
include "elun.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem iccsplit
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( A e. RR /\ B e. RR /\ C e. ( A [,] B ) ) -> ( A [,] B ) = ( ( A [,] C ) u. ( C [,] B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cA
    cB
    cicc
    co
    #
    wcel
    #
    w3a
    #
    vx
    @2
    cA
    cC
    cicc
    co
    #
    cC
    cB
    cicc
    co
    #
    cun
    #
    @4
    vx
    cv
    #
    @2
    wcel
    #
    @8
    @5
    wcel
    #
    @8
    @6
    wcel
    #
    wo
    #
    @8
    @7
    wcel
    @4
    @8
    cr
    wcel
    #
    cA
    @8
    cle
    wbr
    #
    @8
    cB
    cle
    wbr
    #
    w3a
    #
    @13
    @14
    @8
    cC
    cle
    wbr
    #
    w3a
    #
    @13
    cC
    @8
    cle
    wbr
    #
    @15
    w3a
    #
    wo
    #
    @9
    @12
    @4
    @16
    @21
    @4
    @16
    @21
    @4
    @16
    wa
    #
    @21
    @8
    cC
    @22
    @8
    cC
    clt
    wbr
    #
    wa
    #
    @18
    @20
    @24
    @13
    @14
    @17
    @13
    @14
    @15
    @4
    @23
    simplr1
    @13
    @14
    @15
    @4
    @23
    simplr2
    @22
    @23
    @17
    @22
    @13
    cC
    cr
    wcel
    #
    @23
    @17
    wi
    @4
    @13
    @14
    @15
    simpr1
    #
    @4
    @25
    @16
    @0
    @1
    @3
    @25
    @0
    @1
    wa
    #
    @2
    cr
    cC
    cA
    cB
    iccssre
    sseld
    #
    3impia
    adantr
    #
    @8
    cC
    ltle
    syl2anc
    imp
    3jca
    orcd
    @22
    @19
    wa
    #
    @20
    @18
    @30
    @13
    @19
    @15
    @13
    @14
    @15
    @4
    @19
    simplr1
    @22
    @19
    simpr
    @13
    @14
    @15
    @4
    @19
    simplr3
    3jca
    olcd
    @26
    @29
    ltlecasei
    ex
    @4
    @18
    @16
    @20
    @4
    @18
    @13
    @14
    @15
    @18
    @13
    wi
    @4
    @13
    @14
    @17
    simp1
    #
    a1i
    @18
    @14
    wi
    @4
    @13
    @14
    @17
    simp2
    a1i
    @0
    @1
    @3
    @18
    @15
    wi
    #
    @27
    @3
    @25
    cA
    cC
    cle
    wbr
    #
    cC
    cB
    cle
    wbr
    #
    w3a
    #
    @32
    cA
    cB
    cC
    elicc2
    #
    @27
    @35
    @18
    @15
    @27
    @35
    @18
    w3a
    @8
    cC
    cB
    @18
    @27
    @13
    @35
    @31
    3ad2ant3
    @35
    @27
    @25
    @18
    @25
    @33
    @34
    simp1
    #
    3ad2ant2
    @0
    @1
    @35
    @18
    simp1r
    @18
    @27
    @17
    @35
    @13
    @14
    @17
    simp3
    3ad2ant3
    @35
    @27
    @34
    @18
    @25
    @33
    @34
    simp3
    3ad2ant2
    letrd
    3exp
    sylbid
    3impia
    3jcad
    @4
    @20
    @13
    @14
    @15
    @20
    @13
    wi
    @4
    @13
    @19
    @15
    simp1
    #
    a1i
    @0
    @1
    @3
    @20
    @14
    wi
    #
    @27
    @3
    @35
    @39
    @36
    @27
    @35
    @20
    @14
    @27
    @35
    @20
    w3a
    cA
    cC
    @8
    @0
    @1
    @35
    @20
    simp1l
    @35
    @27
    @25
    @20
    @37
    3ad2ant2
    @20
    @27
    @13
    @35
    @38
    3ad2ant3
    @35
    @27
    @33
    @20
    @25
    @33
    @34
    simp2
    3ad2ant2
    @20
    @27
    @19
    @35
    @13
    @19
    @15
    simp2
    3ad2ant3
    letrd
    3exp
    sylbid
    3impia
    @20
    @15
    wi
    @4
    @13
    @19
    @15
    simp3
    a1i
    3jcad
    jaod
    impbid
    @0
    @1
    @9
    @16
    wb
    @3
    cA
    cB
    @8
    elicc2
    3adant3
    @4
    @27
    @25
    wa
    #
    @12
    @21
    wb
    @0
    @1
    @3
    @40
    @27
    @3
    @25
    @28
    imdistani
    3impa
    @40
    @10
    @18
    @11
    @20
    @0
    @25
    @10
    @18
    wb
    @1
    cA
    cC
    @8
    elicc2
    adantlr
    @1
    @25
    @11
    @20
    wb
    #
    @0
    @25
    @1
    @41
    cC
    cB
    @8
    elicc2
    ancoms
    adantll
    orbi12d
    syl
    3bitr4d
    @8
    @5
    @6
    elun
    syl6bbr
    eqrdv
end
