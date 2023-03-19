include "cdmd.mm"
include "wbr.mm"
include "cv.mm"
include "chj.mm"
include "co.mm"
include "wss.mm"
include "cin.mm"
include "wi.mm"
include "cat.mm"
include "wral.mm"
include "wcel.mm"
include "cch.mm"
include "dmdi4.mm"
include "mp3an12.mm"
include "atelch.mm"
include "syl11.mm"
include "a1dd.mm"
include "ralrimiv.mm"
include "cph.mm"
include "wceq.mm"
include "wn.mm"
include "wa.mm"
include "chjcom.mm"
include "sylancr.mm"
include "ineq1d.mm"
include "chjcomi.mm"
include "ineq2i.mm"
include "syl6eqr.mm"
include "adantr.mm"
include "sseq2i.mm"
include "notbii.mm"
include "atabs2i.mm"
include "imp.mm"
include "sylan2b.mm"
include "eqtr3d.mm"
include "chjcl.mm"
include "sylancl.mm"
include "chincl.mm"
include "chub2.mm"
include "eqsstrd.mm"
include "ex.mm"
include "biantrud.mm"
include "pm4.83.mm"
include "syl6bb.mm"
include "ralbiia.mm"
include "sumdmdlem2.mm"
include "sylbi.mm"
include "sumdmdi.mm"
include "sylib.mm"
include "impbii.mm"
include "wb.mm"
include "chub2i.mm"
include "biantru.mm"
include "chjcli.mm"
include "chlub.mm"
include "mp3an23.mm"
include "syl5bb.mm"
include "ssid.mm"
include "biantrur.mm"
include "ssin.mm"
include "bitri.mm"
include "biimpa.mm"
include "inss1.mm"
include "jctil.mm"
include "eqss.mm"
include "sylibr.mm"
include "sseq1d.mm"
include "mpan2.mm"
include "mp3an2.mm"
include "mpdan.mm"
include "bitrd.mm"
include "bitr4d.mm"
include "pm5.74da.mm"
include "syl.mm"

theorem dmdbr5ati
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cC: class C
  assume sumdmdi.1: |- A e. CH
  assume sumdmdi.2: |- B e. CH

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint C y
  disjoint C z
  disjoint C w
  assert |- ( A MH* B <-> A. x e. HAtoms ( x C_ ( A vH B ) -> x C_ ( ( ( x vH B ) i^i A ) vH B ) ) )

  proof
    cA
    cB
    cdmd
    wbr
    #
    vx
    cv
    #
    cA
    cB
    chj
    co
    #
    wss
    #
    @1
    cB
    chj
    co
    #
    @2
    cin
    #
    @4
    cA
    cin
    #
    cB
    chj
    co
    #
    wss
    #
    wi
    #
    vx
    cat
    wral
    #
    @3
    @1
    @7
    wss
    #
    wi
    #
    vx
    cat
    wral
    @0
    @10
    @0
    @9
    vx
    cat
    @0
    @1
    cat
    wcel
    #
    @8
    @3
    @1
    cch
    wcel
    #
    @0
    @8
    @13
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    @14
    @0
    @8
    wi
    sumdmdi.1
    sumdmdi.2
    cA
    cB
    @1
    dmdi4
    mp3an12
    @1
    atelch
    #
    syl11
    a1dd
    ralrimiv
    @10
    cA
    cB
    cph
    co
    @2
    wceq
    #
    @0
    @10
    @8
    vx
    cat
    wral
    @18
    @9
    @8
    vx
    cat
    @13
    @9
    @9
    @3
    wn
    #
    @8
    wi
    #
    wa
    @8
    @13
    @20
    @9
    @13
    @19
    @8
    @13
    @19
    wa
    #
    @5
    cB
    @7
    @21
    cB
    @1
    chj
    co
    #
    cB
    cA
    chj
    co
    #
    cin
    #
    @5
    cB
    @13
    @24
    @5
    wceq
    @19
    @13
    @24
    @4
    @23
    cin
    @5
    @13
    @22
    @4
    @23
    @13
    @16
    @14
    @22
    @4
    wceq
    sumdmdi.2
    @17
    cB
    @1
    chjcom
    sylancr
    ineq1d
    @2
    @23
    @4
    cA
    cB
    sumdmdi.1
    sumdmdi.2
    chjcomi
    #
    ineq2i
    syl6eqr
    adantr
    @19
    @13
    @1
    @23
    wss
    #
    wn
    #
    @24
    cB
    wceq
    #
    @3
    @26
    @2
    @23
    @1
    @25
    sseq2i
    notbii
    @13
    @27
    @28
    cB
    cA
    @1
    sumdmdi.2
    sumdmdi.1
    atabs2i
    imp
    sylan2b
    eqtr3d
    @13
    cB
    @7
    wss
    #
    @19
    @13
    @16
    @6
    cch
    wcel
    #
    @29
    sumdmdi.2
    @13
    @4
    cch
    wcel
    #
    @15
    @30
    @13
    @14
    @16
    @31
    @17
    sumdmdi.2
    @1
    cB
    chjcl
    #
    sylancl
    sumdmdi.1
    @4
    cA
    chincl
    #
    sylancl
    cB
    @6
    chub2
    #
    sylancr
    adantr
    eqsstrd
    ex
    biantrud
    @3
    @8
    pm4.83
    syl6bb
    ralbiia
    vx
    cA
    cB
    sumdmdi.1
    sumdmdi.2
    sumdmdlem2
    sylbi
    cA
    cB
    sumdmdi.1
    sumdmdi.2
    sumdmdi
    sylib
    impbii
    @9
    @12
    vx
    cat
    @13
    @14
    @9
    @12
    wb
    @17
    @14
    @3
    @8
    @11
    @14
    @3
    wa
    #
    @8
    @4
    @7
    wss
    #
    @11
    @35
    @5
    @4
    @7
    @35
    @5
    @4
    wss
    #
    @4
    @5
    wss
    #
    wa
    @5
    @4
    wceq
    @35
    @38
    @37
    @14
    @3
    @38
    @14
    @3
    @4
    @2
    wss
    #
    @38
    @3
    @3
    cB
    @2
    wss
    #
    wa
    #
    @14
    @39
    @40
    @3
    cB
    cA
    sumdmdi.2
    sumdmdi.1
    chub2i
    biantru
    @14
    @16
    @2
    cch
    wcel
    @41
    @39
    wb
    sumdmdi.2
    cA
    cB
    sumdmdi.1
    sumdmdi.2
    chjcli
    @1
    cB
    @2
    chlub
    mp3an23
    syl5bb
    @39
    @4
    @4
    wss
    #
    @39
    wa
    @38
    @42
    @39
    @4
    ssid
    biantrur
    @4
    @4
    @2
    ssin
    bitri
    syl6bb
    biimpa
    @4
    @2
    inss1
    jctil
    @5
    @4
    eqss
    sylibr
    sseq1d
    @14
    @11
    @36
    wb
    @3
    @14
    @11
    @11
    @29
    wa
    #
    @36
    @14
    @29
    @11
    @14
    @16
    @30
    @29
    sumdmdi.2
    @14
    @31
    @15
    @30
    @14
    @16
    @31
    sumdmdi.2
    @32
    mpan2
    sumdmdi.1
    @33
    sylancl
    #
    @34
    sylancr
    biantrud
    @14
    @7
    cch
    wcel
    #
    @43
    @36
    wb
    #
    @14
    @30
    @16
    @45
    @44
    sumdmdi.2
    @6
    cB
    chjcl
    sylancl
    @14
    @16
    @45
    @46
    sumdmdi.2
    @1
    cB
    @7
    chlub
    mp3an2
    mpdan
    bitrd
    adantr
    bitr4d
    pm5.74da
    syl
    ralbiia
    bitri
end
