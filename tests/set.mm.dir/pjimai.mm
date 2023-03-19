include "cpjh.mm"
include "cfv.mm"
include "cima.mm"
include "cort.mm"
include "cph.mm"
include "co.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wrex.mm"
include "cmv.mm"
include "cva.mm"
include "cch.mm"
include "chil.mm"
include "wb.mm"
include "sheli.mm"
include "pjeq.mm"
include "sylancr.mm"
include "ibar.mm"
include "bicomd.mm"
include "sylan9bbr.mm"
include "w3a.mm"
include "cheli.mm"
include "choccli.mm"
include "hvsubadd.mm"
include "3comr.mm"
include "ax-hvcom.mm"
include "3adant2.mm"
include "eqeq1d.mm"
include "bitr4d.mm"
include "syl3an.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "3expa.mm"
include "rexbidva.mm"
include "wfn.mm"
include "wss.mm"
include "pjfni.mm"
include "shssii.mm"
include "fvelimab.mm"
include "mp2an.mm"
include "csh.mm"
include "chshii.mm"
include "shsel3.mm"
include "pm5.32ri.mm"
include "crn.mm"
include "imassrn.mm"
include "pjrni.mm"
include "sseqtri.mm"
include "sseli.mm"
include "pm4.71i.mm"
include "elin.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem pjimai
  let cA: class A
  let cB: class B
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume pjima.1: |- A e. SH
  assume pjima.2: |- B e. CH


  assert |- ( ( projh ` B ) " A ) = ( ( A +H ( _|_ ` B ) ) i^i B )

  proof
    vu
    cB
    cpjh
    cfv
    #
    cA
    cima
    #
    cA
    cB
    cort
    cfv
    #
    cph
    co
    #
    cB
    cin
    #
    vu
    cv
    #
    @1
    wcel
    #
    @5
    cB
    wcel
    #
    wa
    @5
    @3
    wcel
    #
    @7
    wa
    @6
    @5
    @4
    wcel
    @7
    @6
    @8
    @7
    vv
    cv
    #
    @0
    cfv
    @5
    wceq
    #
    vv
    cA
    wrex
    #
    @5
    @9
    vw
    cv
    #
    cmv
    co
    #
    wceq
    #
    vw
    @2
    wrex
    #
    vv
    cA
    wrex
    #
    @6
    @8
    @7
    @10
    @15
    vv
    cA
    @7
    @9
    cA
    wcel
    #
    wa
    #
    @10
    @9
    @5
    @12
    cva
    co
    #
    wceq
    #
    vw
    @2
    wrex
    #
    @15
    @17
    @10
    @7
    @21
    wa
    #
    @7
    @21
    @17
    cB
    cch
    wcel
    @9
    chil
    wcel
    #
    @10
    @22
    wb
    pjima.2
    @9
    cA
    pjima.1
    sheli
    #
    vw
    @9
    @5
    cB
    pjeq
    sylancr
    @7
    @21
    @22
    @7
    @21
    ibar
    bicomd
    sylan9bbr
    @18
    @14
    @20
    vw
    @2
    @7
    @17
    @12
    @2
    wcel
    #
    @14
    @20
    wb
    @7
    @17
    @25
    w3a
    @13
    @5
    wceq
    #
    @19
    @9
    wceq
    #
    @14
    @20
    @7
    @5
    chil
    wcel
    #
    @17
    @23
    @25
    @12
    chil
    wcel
    #
    @26
    @27
    wb
    @5
    cB
    pjima.2
    cheli
    @24
    @12
    @2
    cB
    pjima.2
    choccli
    #
    cheli
    @28
    @23
    @29
    w3a
    #
    @26
    @12
    @5
    cva
    co
    #
    @9
    wceq
    #
    @27
    @23
    @29
    @28
    @26
    @33
    wb
    @9
    @12
    @5
    hvsubadd
    3comr
    @31
    @19
    @32
    @9
    @28
    @29
    @19
    @32
    wceq
    @23
    @5
    @12
    ax-hvcom
    3adant2
    eqeq1d
    bitr4d
    syl3an
    @5
    @13
    eqcom
    @9
    @19
    eqcom
    3bitr4g
    3expa
    rexbidva
    bitr4d
    rexbidva
    @0
    chil
    wfn
    cA
    chil
    wss
    @6
    @11
    wb
    cB
    pjima.2
    pjfni
    cA
    pjima.1
    shssii
    vv
    chil
    cA
    @5
    @0
    fvelimab
    mp2an
    cA
    csh
    wcel
    @2
    csh
    wcel
    @8
    @16
    wb
    pjima.1
    @2
    @30
    chshii
    vv
    vw
    cA
    @2
    @5
    shsel3
    mp2an
    3bitr4g
    pm5.32ri
    @6
    @7
    @1
    cB
    @5
    @1
    @0
    crn
    cB
    @0
    cA
    imassrn
    cB
    pjima.2
    pjrni
    sseqtri
    sseli
    pm4.71i
    @5
    @3
    cB
    elin
    3bitr4i
    eqriv
end
