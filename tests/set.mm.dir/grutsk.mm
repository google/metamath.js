include "cgru.mm"
include "cv.mm"
include "wtr.mm"
include "ctsk.mm"
include "crab.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "0tsk.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "a1i.mm"
include "wne.mm"
include "con0.mm"
include "cin.mm"
include "cr1.mm"
include "cfv.mm"
include "cima.mm"
include "cuni.mm"
include "cvv.mm"
include "vex.mm"
include "unir1.mm"
include "eleqtrri.mm"
include "eqid.mm"
include "grur1.mm"
include "mpan2.mm"
include "adantr.mm"
include "cina.mm"
include "gruina.mm"
include "inatsk.mm"
include "syl.mm"
include "eqeltrd.mm"
include "ex.mm"
include "pm2.61dne.mm"
include "grutr.mm"
include "jca.mm"
include "grutsk1.mm"
include "impbii.mm"
include "treq.mm"
include "elrab.mm"
include "bitr4i.mm"
include "eqriv.mm"

theorem grutsk
  let vx: setvar x
  let vy: setvar y


  assert |- Univ = { x e. Tarski | Tr x }

  proof
    vy
    cgru
    vx
    cv
    #
    wtr
    #
    vx
    ctsk
    crab
    #
    vy
    cv
    #
    cgru
    wcel
    #
    @3
    ctsk
    wcel
    #
    @3
    wtr
    #
    wa
    #
    @3
    @2
    wcel
    @4
    @7
    @4
    @5
    @6
    @4
    @5
    @3
    c0
    @3
    c0
    wceq
    #
    @5
    wi
    @4
    @8
    @5
    c0
    ctsk
    wcel
    0tsk
    @3
    c0
    ctsk
    eleq1
    mpbiri
    a1i
    @4
    @3
    c0
    wne
    #
    @5
    @4
    @9
    wa
    #
    @3
    @3
    con0
    cin
    #
    cr1
    cfv
    #
    ctsk
    @4
    @3
    @12
    wceq
    #
    @9
    @4
    @3
    cr1
    con0
    cima
    cuni
    #
    wcel
    @13
    @3
    cvv
    @14
    vy
    vex
    unir1
    eleqtrri
    @11
    @3
    @11
    eqid
    #
    grur1
    mpan2
    adantr
    @10
    @11
    cina
    wcel
    @12
    ctsk
    wcel
    @11
    @3
    @15
    gruina
    @11
    inatsk
    syl
    eqeltrd
    ex
    pm2.61dne
    @3
    grutr
    jca
    @3
    grutsk1
    impbii
    @1
    @6
    vx
    @3
    ctsk
    @0
    @3
    treq
    elrab
    bitr4i
    eqriv
end
