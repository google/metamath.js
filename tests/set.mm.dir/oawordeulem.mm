include "wss.mm"
include "cv.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "con0.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "cint.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "oaword2.mm"
include "mp2an.mm"
include "oveq2.mm"
include "sseq2d.mm"
include "elrab2.mm"
include "mpbir2an.mm"
include "ne0ii.mm"
include "oninton.mm"
include "csuc.mm"
include "cvv.mm"
include "wlim.mm"
include "w3o.mm"
include "onzsl.mm"
include "mpbi.mm"
include "oa0.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "sseq1d.mm"
include "biimprd.mm"
include "oasuc.mm"
include "mpan.mm"
include "sylan9eqr.mm"
include "vex.mm"
include "sucid.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "oneli.mm"
include "wn.mm"
include "inteqi.mm"
include "eleq2i.mm"
include "onnminsb.mm"
include "syl5bi.mm"
include "wb.mm"
include "oacl.mm"
include "ontri1.mm"
include "sylancr.mm"
include "con2bid.mm"
include "sylibrd.mm"
include "mpcom.mm"
include "word.mm"
include "onordi.mm"
include "ordsucss.mm"
include "3syl.mm"
include "adantl.mm"
include "eqsstrd.mm"
include "rexlimiva.mm"
include "a1d.mm"
include "ciun.mm"
include "oalim.mm"
include "iunss.mm"
include "onelssi.mm"
include "syl.mm"
include "mprgbir.mm"
include "syl6eqss.mm"
include "3jaoi.mm"
include "rspcev.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfint.mm"
include "nfov.mm"
include "nfss.mm"
include "onminsb.mm"
include "oveq2i.mm"
include "sseqtr4i.mm"
include "jctir.mm"
include "eqss.mm"
include "sylibr.mm"
include "eqeq1d.mm"
include "eqtr3.mm"
include "oacan.mm"
include "mp3an1.mm"
include "syl5ib.mm"
include "rgen2a.mm"
include "reu4.mm"

theorem oawordeulem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let vz: setvar z
  assume oawordeulem.1: |- A e. On
  assume oawordeulem.2: |- B e. On
  assume oawordeulem.3: |- S = { y e. On | B C_ ( A +o y ) }

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint S x
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint S z
  assert |- ( A C_ B -> E! x e. On ( A +o x ) = B )

  proof
    cA
    cB
    wss
    #
    cA
    vx
    cv
    #
    coa
    co
    #
    cB
    wceq
    #
    vx
    con0
    wrex
    #
    @3
    cA
    vy
    cv
    #
    coa
    co
    #
    cB
    wceq
    #
    wa
    #
    @1
    @5
    wceq
    #
    wi
    #
    vy
    con0
    wral
    vx
    con0
    wral
    #
    wa
    @3
    vx
    con0
    wreu
    @0
    @4
    @11
    @0
    cS
    cint
    #
    con0
    wcel
    #
    cA
    @12
    coa
    co
    #
    cB
    wceq
    #
    @4
    cS
    con0
    wss
    cS
    c0
    wne
    @13
    cS
    cB
    @6
    wss
    #
    vy
    con0
    crab
    #
    con0
    oawordeulem.3
    @16
    vy
    con0
    ssrab2
    eqsstri
    cB
    cS
    cB
    cS
    wcel
    cB
    con0
    wcel
    #
    cB
    cA
    cB
    coa
    co
    #
    wss
    #
    oawordeulem.2
    @18
    cA
    con0
    wcel
    #
    @20
    oawordeulem.2
    oawordeulem.1
    cB
    cA
    oaword2
    mp2an
    #
    @16
    @20
    vy
    cB
    con0
    cS
    @5
    cB
    wceq
    @6
    @19
    cB
    @5
    cB
    cA
    coa
    oveq2
    sseq2d
    #
    oawordeulem.3
    elrab2
    mpbir2an
    ne0ii
    cS
    oninton
    mp2an
    #
    @0
    @14
    cB
    wss
    #
    cB
    @14
    wss
    #
    wa
    @15
    @0
    @25
    @26
    @12
    c0
    wceq
    #
    @12
    vz
    cv
    #
    csuc
    #
    wceq
    #
    vz
    con0
    wrex
    #
    @12
    cvv
    wcel
    @12
    wlim
    wa
    #
    w3o
    #
    @0
    @25
    wi
    #
    @13
    @33
    @24
    vz
    @12
    onzsl
    mpbi
    @27
    @34
    @31
    @32
    @27
    @25
    @0
    @27
    @14
    cA
    cB
    @27
    @14
    cA
    c0
    coa
    co
    #
    cA
    @12
    c0
    cA
    coa
    oveq2
    @21
    @35
    cA
    wceq
    oawordeulem.1
    cA
    oa0
    ax-mp
    syl6eq
    sseq1d
    biimprd
    @31
    @25
    @0
    @30
    @25
    vz
    con0
    @28
    con0
    wcel
    #
    @30
    wa
    @14
    cA
    @28
    coa
    co
    #
    csuc
    #
    cB
    @30
    @36
    @14
    cA
    @29
    coa
    co
    #
    @38
    @12
    @29
    cA
    coa
    oveq2
    @21
    @36
    @39
    @38
    wceq
    oawordeulem.1
    cA
    @28
    oasuc
    mpan
    sylan9eqr
    @30
    @38
    cB
    wss
    #
    @36
    @30
    @28
    @12
    wcel
    #
    @37
    cB
    wcel
    #
    @40
    @30
    @41
    @28
    @29
    wcel
    @28
    vz
    vex
    sucid
    @12
    @29
    @28
    eleq2
    mpbiri
    @36
    @41
    @42
    @12
    @28
    @24
    oneli
    @36
    @41
    cB
    @37
    wss
    #
    wn
    #
    @42
    @41
    @28
    @17
    cint
    #
    wcel
    @36
    @44
    @12
    @45
    @28
    cS
    @17
    oawordeulem.3
    inteqi
    #
    eleq2i
    @16
    @43
    vy
    @28
    @5
    @28
    wceq
    @6
    @37
    cB
    @5
    @28
    cA
    coa
    oveq2
    sseq2d
    onnminsb
    syl5bi
    @36
    @43
    @42
    @36
    @18
    @37
    con0
    wcel
    #
    @43
    @42
    wn
    wb
    oawordeulem.2
    @21
    @36
    @47
    oawordeulem.1
    cA
    @28
    oacl
    mpan
    cB
    @37
    ontri1
    sylancr
    con2bid
    sylibrd
    mpcom
    #
    cB
    word
    @42
    @40
    wi
    cB
    oawordeulem.2
    onordi
    @37
    cB
    ordsucss
    ax-mp
    3syl
    adantl
    eqsstrd
    rexlimiva
    a1d
    @32
    @25
    @0
    @32
    @14
    vz
    @12
    @37
    ciun
    #
    cB
    @21
    @32
    @14
    @49
    wceq
    oawordeulem.1
    vz
    cA
    @12
    cvv
    oalim
    mpan
    @49
    cB
    wss
    @37
    cB
    wss
    #
    vz
    @12
    vz
    @12
    @37
    cB
    iunss
    @41
    @42
    @50
    @48
    cB
    @37
    oawordeulem.2
    onelssi
    syl
    mprgbir
    syl6eqss
    a1d
    3jaoi
    ax-mp
    cB
    cA
    @45
    coa
    co
    #
    @14
    @16
    vy
    con0
    wrex
    #
    cB
    @51
    wss
    #
    @18
    @20
    @52
    oawordeulem.2
    @22
    @16
    @20
    vy
    cB
    con0
    @23
    rspcev
    mp2an
    @16
    @53
    vy
    vy
    cB
    @51
    vy
    cB
    nfcv
    vy
    cA
    @45
    coa
    vy
    cA
    nfcv
    vy
    coa
    nfcv
    vy
    @17
    @16
    vy
    con0
    nfrab1
    nfint
    nfov
    nfss
    @5
    @45
    wceq
    @6
    @51
    cB
    @5
    @45
    cA
    coa
    oveq2
    sseq2d
    onminsb
    ax-mp
    @12
    @45
    cA
    coa
    @46
    oveq2i
    sseqtr4i
    jctir
    @14
    cB
    eqss
    sylibr
    @3
    @15
    vx
    @12
    con0
    @1
    @12
    wceq
    @2
    @14
    cB
    @1
    @12
    cA
    coa
    oveq2
    eqeq1d
    rspcev
    sylancr
    @10
    vx
    vy
    con0
    @8
    @2
    @6
    wceq
    #
    @1
    con0
    wcel
    #
    @5
    con0
    wcel
    #
    wa
    @9
    @2
    @6
    cB
    eqtr3
    @21
    @55
    @56
    @54
    @9
    wb
    oawordeulem.1
    cA
    @1
    @5
    oacan
    mp3an1
    syl5ib
    rgen2a
    jctir
    @3
    @7
    vx
    vy
    con0
    @9
    @2
    @6
    cB
    @1
    @5
    cA
    coa
    oveq2
    eqeq1d
    reu4
    sylibr
end
