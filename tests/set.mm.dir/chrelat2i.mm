include "wss.mm"
include "wn.mm"
include "cv.mm"
include "wa.mm"
include "cat.mm"
include "wrex.mm"
include "cin.mm"
include "wpss.mm"
include "nssinpss.mm"
include "chj.mm"
include "co.mm"
include "chincli.mm"
include "chrelati.mm"
include "wcel.mm"
include "cch.mm"
include "wi.mm"
include "atelch.mm"
include "wb.mm"
include "chlub.mm"
include "mp3an13.mm"
include "simpr.mm"
include "syl6bir.mm"
include "adantld.mm"
include "ssin.mm"
include "notbii.mm"
include "chnle.mm"
include "mpan.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "pm3.21.mm"
include "wo.mm"
include "orcom.mm"
include "pm4.55.mm"
include "imor.mm"
include "3bitr4ri.mm"
include "sylib.mm"
include "con2i.mm"
include "adantrl.mm"
include "jcad.mm"
include "syl.mm"
include "reximia.mm"
include "sylbi.mm"
include "wral.mm"
include "sstr2.mm"
include "com12.mm"
include "ralrimivw.mm"
include "iman.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitri.mm"
include "impbii.mm"

theorem chrelat2i
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume chpssat.1: |- A e. CH
  assume chpssat.2: |- B e. CH

  disjoint A x
  disjoint B x
  assert |- ( -. A C_ B <-> E. x e. HAtoms ( x C_ A /\ -. x C_ B ) )

  proof
    cA
    cB
    wss
    #
    wn
    #
    vx
    cv
    #
    cA
    wss
    #
    @2
    cB
    wss
    #
    wn
    #
    wa
    #
    vx
    cat
    wrex
    #
    @1
    cA
    cB
    cin
    #
    cA
    wpss
    #
    @7
    cA
    cB
    nssinpss
    @9
    @8
    @8
    @2
    chj
    co
    #
    wpss
    #
    @10
    cA
    wss
    #
    wa
    #
    vx
    cat
    wrex
    @7
    vx
    @8
    cA
    cA
    cB
    chpssat.1
    chpssat.2
    chincli
    #
    chpssat.1
    chrelati
    @13
    @6
    vx
    cat
    @2
    cat
    wcel
    @2
    cch
    wcel
    #
    @13
    @6
    wi
    @2
    atelch
    @15
    @13
    @3
    @5
    @15
    @12
    @3
    @11
    @15
    @12
    @8
    cA
    wss
    #
    @3
    wa
    #
    @3
    @8
    cch
    wcel
    #
    @15
    cA
    cch
    wcel
    @17
    @12
    wb
    @14
    chpssat.1
    @8
    @2
    cA
    chlub
    mp3an13
    #
    @16
    @3
    simpr
    syl6bir
    adantld
    @15
    @13
    @3
    @4
    wa
    #
    wn
    #
    @17
    wa
    @5
    @15
    @21
    @11
    @17
    @12
    @21
    @2
    @8
    wss
    #
    wn
    #
    @15
    @11
    @20
    @22
    @2
    cA
    cB
    ssin
    notbii
    @18
    @15
    @23
    @11
    wb
    @14
    @8
    @2
    chnle
    mpan
    syl5bb
    @19
    anbi12d
    @21
    @3
    @5
    @16
    @4
    @21
    @3
    wa
    #
    @4
    @3
    @20
    wi
    #
    @24
    wn
    #
    @4
    @3
    pm3.21
    @20
    @3
    wn
    #
    wo
    @27
    @20
    wo
    @26
    @25
    @20
    @27
    orcom
    @20
    @3
    pm4.55
    @3
    @20
    imor
    3bitr4ri
    sylib
    con2i
    adantrl
    syl6bir
    jcad
    syl
    reximia
    syl
    sylbi
    @0
    @7
    @0
    @3
    @4
    wi
    #
    vx
    cat
    wral
    #
    @7
    wn
    #
    @0
    @28
    vx
    cat
    @3
    @0
    @4
    @2
    cA
    cB
    sstr2
    com12
    ralrimivw
    @29
    @6
    wn
    #
    vx
    cat
    wral
    @30
    @28
    @31
    vx
    cat
    @3
    @4
    iman
    ralbii
    @6
    vx
    cat
    ralnex
    bitri
    sylib
    con2i
    impbii
end
