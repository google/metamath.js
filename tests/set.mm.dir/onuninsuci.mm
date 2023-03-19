include "cv.mm"
include "csuc.mm"
include "wceq.mm"
include "con0.mm"
include "wrex.mm"
include "cuni.mm"
include "wn.mm"
include "wa.mm"
include "wcel.mm"
include "onirri.mm"
include "id.mm"
include "cun.mm"
include "csn.mm"
include "df-suc.mm"
include "eqeq2i.mm"
include "unieq.mm"
include "sylbi.mm"
include "uniun.mm"
include "vex.mm"
include "unisn.mm"
include "uneq2i.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "wss.mm"
include "wtr.mm"
include "tron.mm"
include "eleq1.mm"
include "mpbii.mm"
include "trsuc.mm"
include "sylancr.mm"
include "word.mm"
include "eloni.mm"
include "ordtr.mm"
include "syl.mm"
include "df-tr.mm"
include "sylib.mm"
include "ssequn1.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "sucid.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "mto.mm"
include "imnani.mm"
include "rexlimivw.mm"
include "onuni.mm"
include "ax-mp.mm"
include "onuniorsuci.mm"
include "ori.mm"
include "suceq.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "impbii.mm"
include "con2bii.mm"

theorem onuninsuci
  let vx: setvar x
  let cA: class A
  assume onssi.1: |- A e. On

  disjoint A x
  assert |- ( A = U. A <-> -. E. x e. On A = suc x )

  proof
    cA
    vx
    cv
    #
    csuc
    #
    wceq
    #
    vx
    con0
    wrex
    #
    cA
    cA
    cuni
    #
    wceq
    #
    @3
    @5
    wn
    #
    @2
    @6
    vx
    con0
    @2
    @5
    @2
    @5
    wa
    #
    cA
    cA
    wcel
    cA
    onssi.1
    onirri
    @7
    cA
    @0
    cA
    @5
    @2
    cA
    @4
    @0
    @5
    id
    @2
    @4
    @0
    cuni
    #
    @0
    cun
    #
    @0
    @2
    @4
    @0
    @0
    csn
    #
    cun
    #
    cuni
    #
    @9
    @2
    cA
    @11
    wceq
    @4
    @12
    wceq
    @1
    @11
    cA
    @0
    df-suc
    eqeq2i
    cA
    @11
    unieq
    sylbi
    @12
    @8
    @10
    cuni
    #
    cun
    @9
    @0
    @10
    uniun
    @13
    @0
    @8
    @0
    vx
    vex
    #
    unisn
    uneq2i
    eqtri
    syl6eq
    @2
    @8
    @0
    wss
    #
    @9
    @0
    wceq
    @2
    @0
    con0
    wcel
    #
    @15
    @2
    con0
    wtr
    @1
    con0
    wcel
    #
    @16
    tron
    @2
    cA
    con0
    wcel
    #
    @17
    onssi.1
    cA
    @1
    con0
    eleq1
    mpbii
    con0
    @0
    trsuc
    sylancr
    @16
    @0
    wtr
    #
    @15
    @16
    @0
    word
    @19
    @0
    eloni
    @0
    ordtr
    syl
    @0
    df-tr
    sylib
    syl
    @8
    @0
    ssequn1
    sylib
    eqtrd
    sylan9eqr
    @2
    @0
    cA
    wcel
    #
    @5
    @2
    @20
    @0
    @1
    wcel
    @0
    @14
    sucid
    cA
    @1
    @0
    eleq2
    mpbiri
    adantr
    eqeltrd
    mto
    imnani
    rexlimivw
    @6
    @4
    con0
    wcel
    #
    cA
    @4
    csuc
    #
    wceq
    #
    @3
    @18
    @21
    onssi.1
    cA
    onuni
    ax-mp
    @5
    @23
    cA
    onssi.1
    onuniorsuci
    ori
    @2
    @23
    vx
    @4
    con0
    @0
    @4
    wceq
    @1
    @22
    cA
    @0
    @4
    suceq
    eqeq2d
    rspcev
    sylancr
    impbii
    con2bii
end
