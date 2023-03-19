include "cv.mm"
include "wss.mm"
include "cat.mm"
include "crab.mm"
include "chsup.mm"
include "cfv.mm"
include "cch.mm"
include "wcel.mm"
include "ssrab2.mm"
include "atssch.mm"
include "sstri.mm"
include "chsupcl.mm"
include "ax-mp.mm"
include "chshii.mm"
include "wa.mm"
include "atelch.mm"
include "anim1i.mm"
include "sseq1.mm"
include "elrab.mm"
include "3imtr4i.mm"
include "ssriv.mm"
include "wi.mm"
include "chsupss.mm"
include "mp2an.mm"
include "wceq.mm"
include "chsupid.mm"
include "sseqtri.mm"
include "cort.mm"
include "cin.mm"
include "wrex.mm"
include "wn.mm"
include "c0h.mm"
include "cuni.mm"
include "elssuni.mm"
include "sylbir.mm"
include "chsupunss.mm"
include "syl6ss.mm"
include "ex.mm"
include "wne.mm"
include "atne0.mm"
include "adantr.mm"
include "ssin.mm"
include "chocini.mm"
include "sseq2i.mm"
include "bitr2i.mm"
include "wb.mm"
include "chle0.mm"
include "syl.mm"
include "syl5bbr.mm"
include "biimpa.mm"
include "expr.mm"
include "necon3ad.mm"
include "mpd.mm"
include "syld.mm"
include "imnan.mm"
include "sylib.mm"
include "sylnib.mm"
include "nrex.mm"
include "choccli.mm"
include "chincli.mm"
include "hatomici.mm"
include "necon1bi.mm"
include "omlsii.mm"
include "eqcomi.mm"

theorem hatomistici
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  assume hatomistic.1: |- A e. CH

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- A = ( \/H ` { x e. HAtoms | x C_ A } )

  proof
    vx
    cv
    #
    cA
    wss
    #
    vx
    cat
    crab
    #
    chsup
    cfv
    #
    cA
    @3
    cA
    @2
    cch
    wss
    #
    @3
    cch
    wcel
    @2
    cat
    cch
    @1
    vx
    cat
    ssrab2
    atssch
    sstri
    #
    @2
    chsupcl
    ax-mp
    #
    cA
    hatomistic.1
    chshii
    @3
    @1
    vx
    cch
    crab
    #
    chsup
    cfv
    #
    cA
    @2
    @7
    wss
    #
    @3
    @8
    wss
    #
    vy
    @2
    @7
    vy
    cv
    #
    cat
    wcel
    #
    @11
    cA
    wss
    #
    wa
    #
    @11
    cch
    wcel
    #
    @13
    wa
    @11
    @2
    wcel
    #
    @11
    @7
    wcel
    @12
    @15
    @13
    @11
    atelch
    #
    anim1i
    @1
    @13
    vx
    @11
    cat
    @0
    @11
    cA
    sseq1
    #
    elrab
    #
    @1
    @13
    vx
    @11
    cch
    @18
    elrab
    3imtr4i
    ssriv
    @4
    @7
    cch
    wss
    @9
    @10
    wi
    @5
    @1
    vx
    cch
    ssrab2
    @2
    @7
    chsupss
    mp2an
    ax-mp
    cA
    cch
    wcel
    @8
    cA
    wceq
    hatomistic.1
    vx
    cA
    chsupid
    ax-mp
    sseqtri
    @11
    cA
    @3
    cort
    cfv
    #
    cin
    #
    wss
    #
    vy
    cat
    wrex
    #
    wn
    @21
    c0h
    wceq
    @22
    vy
    cat
    @12
    @13
    @11
    @20
    wss
    #
    wa
    #
    @22
    @12
    @13
    @24
    wn
    #
    wi
    @25
    wn
    @12
    @13
    @11
    @3
    wss
    #
    @26
    @12
    @13
    @27
    @14
    @11
    @2
    cuni
    #
    @3
    @14
    @16
    @11
    @28
    wss
    @19
    @11
    @2
    elssuni
    sylbir
    @4
    @28
    @3
    wss
    @5
    @2
    chsupunss
    ax-mp
    syl6ss
    ex
    @12
    @27
    @26
    @12
    @27
    wa
    #
    @11
    c0h
    wne
    #
    @26
    @12
    @30
    @27
    @11
    atne0
    adantr
    @29
    @24
    @11
    c0h
    @12
    @27
    @24
    @11
    c0h
    wceq
    #
    @12
    @27
    @24
    wa
    #
    @31
    @32
    @11
    c0h
    wss
    #
    @12
    @31
    @32
    @11
    @3
    @20
    cin
    #
    wss
    @33
    @11
    @3
    @20
    ssin
    @34
    c0h
    @11
    @3
    @6
    chocini
    sseq2i
    bitr2i
    @12
    @15
    @33
    @31
    wb
    @17
    @11
    chle0
    syl
    syl5bbr
    biimpa
    expr
    necon3ad
    mpd
    ex
    syld
    @13
    @24
    imnan
    sylib
    @11
    cA
    @20
    ssin
    sylnib
    nrex
    @23
    @21
    c0h
    vy
    @21
    cA
    @20
    hatomistic.1
    @3
    @6
    choccli
    chincli
    hatomici
    necon1bi
    ax-mp
    omlsii
    eqcomi
end
