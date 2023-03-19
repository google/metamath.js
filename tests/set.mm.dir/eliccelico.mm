include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cicc.mm"
include "co.mm"
include "cico.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "clt.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simprl.mm"
include "elicc1.mm"
include "biimpa.mm"
include "simp1d.mm"
include "syl21anc.mm"
include "simp3d.mm"
include "jca.mm"
include "simprr.mm"
include "simp2d.mm"
include "syl2anc.mm"
include "elico1.mm"
include "notbid.mm"
include "df-3an.mm"
include "notbii.mm"
include "imnan.mm"
include "bitr4i.mm"
include "sylib.mm"
include "imp.mm"
include "syl22anc.mm"
include "xeqlelt.mm"
include "biimpar.mm"
include "ex.mm"
include "pm5.6.mm"
include "icossicc.mm"
include "simpr.mm"
include "sseldi.mm"
include "eqeltrd.mm"
include "simpl3.mm"
include "breqtrrd.mm"
include "xrleid.mm"
include "syl.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "mpbir3and.mm"
include "jaodan.mm"
include "impbid.mm"

theorem eliccelico
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ A <_ B ) -> ( C e. ( A [,] B ) <-> ( C e. ( A [,) B ) \/ C = B ) ) )

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
    cle
    wbr
    #
    w3a
    #
    cC
    cA
    cB
    cicc
    co
    #
    wcel
    #
    cC
    cA
    cB
    cico
    co
    #
    wcel
    #
    cC
    cB
    wceq
    #
    wo
    #
    @3
    @5
    @7
    wn
    #
    wa
    #
    @8
    wi
    @5
    @9
    wi
    @3
    @11
    @8
    @3
    @11
    wa
    #
    cC
    cxr
    wcel
    #
    @1
    cC
    cB
    cle
    wbr
    #
    cC
    cB
    clt
    wbr
    #
    wn
    #
    @8
    @12
    @0
    @1
    @5
    @13
    @0
    @1
    @2
    @11
    simpl1
    #
    @0
    @1
    @2
    @11
    simpl2
    #
    @3
    @5
    @10
    simprl
    #
    @0
    @1
    wa
    #
    @5
    wa
    #
    @13
    cA
    cC
    cle
    wbr
    #
    @14
    @20
    @5
    @13
    @22
    @14
    w3a
    #
    cA
    cB
    cC
    elicc1
    #
    biimpa
    #
    simp1d
    syl21anc
    #
    @18
    @12
    @0
    @1
    @5
    @14
    @17
    @18
    @19
    @21
    @13
    @22
    @14
    @25
    simp3d
    syl21anc
    @12
    @20
    @10
    @13
    @22
    @16
    @12
    @0
    @1
    @17
    @18
    jca
    #
    @3
    @5
    @10
    simprr
    @26
    @12
    @20
    @5
    @22
    @27
    @19
    @21
    @13
    @22
    @14
    @25
    simp2d
    syl2anc
    @20
    @10
    wa
    #
    @13
    @22
    wa
    #
    @16
    @28
    @13
    @22
    @15
    w3a
    #
    wn
    #
    @29
    @16
    wi
    #
    @20
    @10
    @31
    @20
    @7
    @30
    cA
    cB
    cC
    elico1
    notbid
    biimpa
    @31
    @29
    @15
    wa
    #
    wn
    @32
    @30
    @33
    @13
    @22
    @15
    df-3an
    notbii
    @29
    @15
    imnan
    bitr4i
    sylib
    imp
    syl22anc
    @13
    @1
    wa
    @8
    @14
    @16
    wa
    cC
    cB
    xeqlelt
    biimpar
    syl22anc
    ex
    @5
    @7
    @8
    pm5.6
    sylib
    @3
    @9
    @5
    @3
    @7
    @5
    @8
    @3
    @7
    wa
    @6
    @4
    cC
    cA
    cB
    icossicc
    @3
    @7
    simpr
    sseldi
    @3
    @8
    wa
    #
    @5
    @13
    @22
    @14
    @34
    cC
    cB
    cxr
    @3
    @8
    simpr
    #
    @0
    @1
    @2
    @8
    simpl2
    #
    eqeltrd
    @34
    cA
    cB
    cC
    cle
    @0
    @1
    @2
    @8
    simpl3
    @35
    breqtrrd
    @34
    cC
    cB
    cB
    cle
    @35
    @34
    @1
    cB
    cB
    cle
    wbr
    @36
    cB
    xrleid
    syl
    eqbrtrd
    @34
    @0
    @1
    @5
    @23
    wb
    @0
    @1
    @2
    @8
    simpl1
    @36
    @24
    syl2anc
    mpbir3and
    jaodan
    ex
    impbid
end
