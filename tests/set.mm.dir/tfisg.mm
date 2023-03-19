include "cv.mm"
include "wsbc.mm"
include "wral.mm"
include "wi.mm"
include "con0.mm"
include "crab.mm"
include "wceq.mm"
include "wss.mm"
include "wcel.mm"
include "ssrab2.mm"
include "wa.mm"
include "dfss3.mm"
include "nfcv.mm"
include "elrabsf.mm"
include "simprbi.mm"
include "ralimi.mm"
include "sylbi.mm"
include "nfsbc1v.mm"
include "nfral.mm"
include "nfim.mm"
include "raleq.mm"
include "sbceq1a.mm"
include "imbi12d.mm"
include "rspc.mm"
include "impcom.mm"
include "syl5.mm"
include "simpr.mm"
include "jctild.mm"
include "syl6ibr.mm"
include "ralrimiva.mm"
include "tfi.mm"
include "sylancr.mm"
include "eqcomd.mm"
include "rabid2.mm"
include "sylib.mm"

theorem tfisg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint ph y
  disjoint x y
  disjoint ph z
  disjoint y z
  disjoint x z
  assert |- ( A. x e. On ( A. y e. x [. y / x ]. ph -> ph ) -> A. x e. On ph )

  proof
    wph
    vx
    vy
    cv
    #
    wsbc
    #
    vy
    vx
    cv
    #
    wral
    #
    wph
    wi
    #
    vx
    con0
    wral
    #
    con0
    wph
    vx
    con0
    crab
    #
    wceq
    wph
    vx
    con0
    wral
    @5
    @6
    con0
    @5
    @6
    con0
    wss
    vz
    cv
    #
    @6
    wss
    #
    @7
    @6
    wcel
    #
    wi
    #
    vz
    con0
    wral
    @6
    con0
    wceq
    wph
    vx
    con0
    ssrab2
    @5
    @10
    vz
    con0
    @5
    @7
    con0
    wcel
    #
    wa
    #
    @8
    @11
    wph
    vx
    @7
    wsbc
    #
    wa
    @9
    @12
    @8
    @13
    @11
    @8
    @1
    vy
    @7
    wral
    #
    @12
    @13
    @8
    @0
    @6
    wcel
    #
    vy
    @7
    wral
    @14
    vy
    @7
    @6
    dfss3
    @15
    @1
    vy
    @7
    @15
    @0
    con0
    wcel
    @1
    wph
    vx
    @0
    con0
    vx
    con0
    nfcv
    #
    elrabsf
    simprbi
    ralimi
    sylbi
    @11
    @5
    @14
    @13
    wi
    #
    @4
    @17
    vx
    @7
    con0
    @14
    @13
    vx
    @1
    vx
    vy
    @7
    vx
    @7
    nfcv
    wph
    vx
    @0
    nfsbc1v
    nfral
    wph
    vx
    @7
    nfsbc1v
    nfim
    @2
    @7
    wceq
    @3
    @14
    wph
    @13
    @1
    vy
    @2
    @7
    raleq
    wph
    vx
    @7
    sbceq1a
    imbi12d
    rspc
    impcom
    syl5
    @5
    @11
    simpr
    jctild
    wph
    vx
    @7
    con0
    @16
    elrabsf
    syl6ibr
    ralrimiva
    vz
    @6
    tfi
    sylancr
    eqcomd
    wph
    vx
    con0
    rabid2
    sylib
end
