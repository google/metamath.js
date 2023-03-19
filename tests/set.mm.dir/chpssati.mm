include "wpss.mm"
include "wss.mm"
include "wn.mm"
include "cv.mm"
include "wa.mm"
include "cat.mm"
include "wrex.mm"
include "dfpss3.mm"
include "simprbi.mm"
include "wral.mm"
include "wi.mm"
include "iman.mm"
include "ralbii.mm"
include "crab.mm"
include "ss2rab.mm"
include "chsup.mm"
include "cfv.mm"
include "cch.mm"
include "ssrab2.mm"
include "atssch.mm"
include "sstri.mm"
include "chsupss.mm"
include "mp2an.mm"
include "hatomistici.mm"
include "3sstr4g.mm"
include "sylbir.mm"
include "con3i.mm"
include "dfrex2.mm"
include "sylibr.mm"
include "syl.mm"

theorem chpssati
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume chpssat.1: |- A e. CH
  assume chpssat.2: |- B e. CH

  disjoint A x
  disjoint B x
  assert |- ( A C. B -> E. x e. HAtoms ( x C_ B /\ -. x C_ A ) )

  proof
    cA
    cB
    wpss
    #
    cB
    cA
    wss
    #
    wn
    #
    vx
    cv
    #
    cB
    wss
    #
    @3
    cA
    wss
    #
    wn
    wa
    #
    vx
    cat
    wrex
    #
    @0
    cA
    cB
    wss
    @2
    cA
    cB
    dfpss3
    simprbi
    @2
    @6
    wn
    #
    vx
    cat
    wral
    #
    wn
    @7
    @9
    @1
    @9
    @4
    @5
    wi
    #
    vx
    cat
    wral
    #
    @1
    @10
    @8
    vx
    cat
    @4
    @5
    iman
    ralbii
    @11
    @4
    vx
    cat
    crab
    #
    @5
    vx
    cat
    crab
    #
    wss
    #
    @1
    @4
    @5
    vx
    cat
    ss2rab
    @14
    @12
    chsup
    cfv
    #
    @13
    chsup
    cfv
    #
    cB
    cA
    @12
    cch
    wss
    @13
    cch
    wss
    @14
    @15
    @16
    wss
    wi
    @12
    cat
    cch
    @4
    vx
    cat
    ssrab2
    atssch
    sstri
    @13
    cat
    cch
    @5
    vx
    cat
    ssrab2
    atssch
    sstri
    @12
    @13
    chsupss
    mp2an
    vx
    cB
    chpssat.2
    hatomistici
    vx
    cA
    chpssat.1
    hatomistici
    3sstr4g
    sylbir
    sylbir
    con3i
    @6
    vx
    cat
    dfrex2
    sylibr
    syl
end
