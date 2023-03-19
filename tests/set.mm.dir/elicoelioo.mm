include "cxr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cico.mm"
include "co.mm"
include "wceq.mm"
include "cioo.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "cle.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simprl.mm"
include "elico1.mm"
include "biimpa.mm"
include "simp1d.mm"
include "syl21anc.mm"
include "simp2d.mm"
include "jca.mm"
include "simprr.mm"
include "simp3d.mm"
include "syl2anc.mm"
include "elioo1.mm"
include "notbid.mm"
include "3anan32.mm"
include "notbii.mm"
include "imnan.mm"
include "bitr4i.mm"
include "sylib.mm"
include "imp.mm"
include "syl22anc.mm"
include "xeqlelt.mm"
include "biimpar.mm"
include "ex.mm"
include "eqcom.mm"
include "syl6ib.mm"
include "pm5.6.mm"
include "orcom.mm"
include "simpr.mm"
include "eqeltrd.mm"
include "xrleid.mm"
include "syl.mm"
include "breqtrrd.mm"
include "simpl3.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "mpbir3and.mm"
include "ioossico.mm"
include "sseldi.mm"
include "jaodan.mm"
include "impbid.mm"

theorem elicoelioo
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ A < B ) -> ( C e. ( A [,) B ) <-> ( C = A \/ C e. ( A (,) B ) ) ) )

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
    clt
    wbr
    #
    w3a
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
    cA
    wceq
    #
    cC
    cA
    cB
    cioo
    co
    #
    wcel
    #
    wo
    #
    @3
    @5
    @8
    @6
    wo
    #
    @9
    @3
    @5
    @8
    wn
    #
    wa
    #
    @6
    wi
    @5
    @10
    wi
    @3
    @12
    cA
    cC
    wceq
    #
    @6
    @3
    @12
    @13
    @3
    @12
    wa
    #
    @0
    cC
    cxr
    wcel
    #
    cA
    cC
    cle
    wbr
    #
    cA
    cC
    clt
    wbr
    #
    wn
    #
    @13
    @0
    @1
    @2
    @12
    simpl1
    #
    @14
    @0
    @1
    @5
    @15
    @19
    @0
    @1
    @2
    @12
    simpl2
    #
    @3
    @5
    @11
    simprl
    #
    @0
    @1
    wa
    #
    @5
    wa
    #
    @15
    @16
    cC
    cB
    clt
    wbr
    #
    @22
    @5
    @15
    @16
    @24
    w3a
    #
    cA
    cB
    cC
    elico1
    #
    biimpa
    #
    simp1d
    syl21anc
    #
    @14
    @0
    @1
    @5
    @16
    @19
    @20
    @21
    @23
    @15
    @16
    @24
    @27
    simp2d
    syl21anc
    @14
    @22
    @11
    @15
    @24
    @18
    @14
    @0
    @1
    @19
    @20
    jca
    #
    @3
    @5
    @11
    simprr
    @28
    @14
    @22
    @5
    @24
    @29
    @21
    @23
    @15
    @16
    @24
    @27
    simp3d
    syl2anc
    @22
    @11
    wa
    #
    @15
    @24
    wa
    #
    @18
    @30
    @15
    @17
    @24
    w3a
    #
    wn
    #
    @31
    @18
    wi
    #
    @22
    @11
    @33
    @22
    @8
    @32
    cA
    cB
    cC
    elioo1
    notbid
    biimpa
    @33
    @31
    @17
    wa
    #
    wn
    @34
    @32
    @35
    @15
    @17
    @24
    3anan32
    notbii
    @31
    @17
    imnan
    bitr4i
    sylib
    imp
    syl22anc
    @0
    @15
    wa
    @13
    @16
    @18
    wa
    cA
    cC
    xeqlelt
    biimpar
    syl22anc
    ex
    cA
    cC
    eqcom
    syl6ib
    @5
    @8
    @6
    pm5.6
    sylib
    @8
    @6
    orcom
    syl6ib
    @3
    @9
    @5
    @3
    @6
    @5
    @8
    @3
    @6
    wa
    #
    @5
    @15
    @16
    @24
    @36
    cC
    cA
    cxr
    @3
    @6
    simpr
    #
    @0
    @1
    @2
    @6
    simpl1
    #
    eqeltrd
    @36
    cA
    cA
    cC
    cle
    @36
    @0
    cA
    cA
    cle
    wbr
    @38
    cA
    xrleid
    syl
    @37
    breqtrrd
    @36
    cC
    cA
    cB
    clt
    @37
    @0
    @1
    @2
    @6
    simpl3
    eqbrtrd
    @36
    @0
    @1
    @5
    @25
    wb
    @38
    @0
    @1
    @2
    @6
    simpl2
    @26
    syl2anc
    mpbir3and
    @3
    @8
    wa
    @7
    @4
    cC
    cA
    cB
    ioossico
    @3
    @8
    simpr
    sseldi
    jaodan
    ex
    impbid
end
