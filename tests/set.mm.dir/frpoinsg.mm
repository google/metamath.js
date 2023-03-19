include "wfr.mm"
include "wpo.mm"
include "wse.mm"
include "w3a.mm"
include "crab.mm"
include "wceq.mm"
include "wral.mm"
include "wss.mm"
include "cv.mm"
include "cpred.mm"
include "wcel.mm"
include "wi.mm"
include "wa.mm"
include "wsbc.mm"
include "dfss3.mm"
include "nfcv.mm"
include "elrabsf.mm"
include "simprbi.mm"
include "ralimi.mm"
include "sylbi.mm"
include "nfv.mm"
include "nfsbc1v.mm"
include "nfral.mm"
include "nfim.mm"
include "weq.mm"
include "eleq1w.mm"
include "anbi2d.mm"
include "predeq3.mm"
include "raleqdv.mm"
include "sbceq1a.mm"
include "imbi12d.mm"
include "chvar.mm"
include "syl5.mm"
include "simpr.mm"
include "jctild.mm"
include "syl6ibr.mm"
include "ralrimiva.mm"
include "ssrab2.mm"
include "jctil.mm"
include "frpoind.mm"
include "mpdan.mm"
include "rabid2.mm"
include "sylib.mm"

theorem frpoinsg
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  let vw: setvar w
  assume frpoinsg.1: |- ( ( ( R Fr A /\ R Po A /\ R Se A ) /\ y e. A ) -> ( A. z e. Pred ( R , A , y ) [. z / y ]. ph -> ph ) )

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint ph z
  disjoint R y
  disjoint R z
  disjoint A w
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint R w
  assert |- ( ( R Fr A /\ R Po A /\ R Se A ) -> A. y e. A ph )

  proof
    cA
    cR
    wfr
    cA
    cR
    wpo
    cA
    cR
    wse
    w3a
    #
    cA
    wph
    vy
    cA
    crab
    #
    wceq
    #
    wph
    vy
    cA
    wral
    @0
    @1
    cA
    wss
    #
    cA
    cR
    vw
    cv
    #
    cpred
    #
    @1
    wss
    #
    @4
    @1
    wcel
    #
    wi
    #
    vw
    cA
    wral
    #
    wa
    @2
    @0
    @9
    @3
    @0
    @8
    vw
    cA
    @0
    @4
    cA
    wcel
    #
    wa
    #
    @6
    @10
    wph
    vy
    @4
    wsbc
    #
    wa
    @7
    @11
    @6
    @12
    @10
    @6
    wph
    vy
    vz
    cv
    #
    wsbc
    #
    vz
    @5
    wral
    #
    @11
    @12
    @6
    @13
    @1
    wcel
    #
    vz
    @5
    wral
    @15
    vz
    @5
    @1
    dfss3
    @16
    @14
    vz
    @5
    @16
    @13
    cA
    wcel
    @14
    wph
    vy
    @13
    cA
    vy
    cA
    nfcv
    #
    elrabsf
    simprbi
    ralimi
    sylbi
    @0
    vy
    cv
    #
    cA
    wcel
    #
    wa
    #
    @14
    vz
    cA
    cR
    @18
    cpred
    #
    wral
    #
    wph
    wi
    #
    wi
    @11
    @15
    @12
    wi
    #
    wi
    vy
    vw
    @11
    @24
    vy
    @11
    vy
    nfv
    @15
    @12
    vy
    @14
    vy
    vz
    @5
    vy
    @5
    nfcv
    wph
    vy
    @13
    nfsbc1v
    nfral
    wph
    vy
    @4
    nfsbc1v
    nfim
    nfim
    vy
    vw
    weq
    #
    @20
    @11
    @23
    @24
    @25
    @19
    @10
    @0
    vy
    vw
    cA
    eleq1w
    anbi2d
    @25
    @22
    @15
    wph
    @12
    @25
    @14
    vz
    @21
    @5
    cA
    cR
    @18
    @4
    predeq3
    raleqdv
    wph
    vy
    @4
    sbceq1a
    imbi12d
    imbi12d
    frpoinsg.1
    chvar
    syl5
    @0
    @10
    simpr
    jctild
    wph
    vy
    @4
    cA
    @17
    elrabsf
    syl6ibr
    ralrimiva
    wph
    vy
    cA
    ssrab2
    jctil
    vw
    cA
    @1
    cR
    frpoind
    mpdan
    wph
    vy
    cA
    rabid2
    sylib
end
