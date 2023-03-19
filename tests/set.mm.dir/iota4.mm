include "weu.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "cio.mm"
include "wsbc.mm"
include "df-eu.mm"
include "wsb.mm"
include "wi.mm"
include "biimpr.mm"
include "alimi.mm"
include "sb2.mm"
include "syl.mm"
include "cv.mm"
include "wceq.mm"
include "iotaval.mm"
include "eqcomd.mm"
include "dfsbcq2.mm"
include "mpbid.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem iota4
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let wps: wff ps
  let vy: setvar y


  assert |- ( E! x ph -> [. ( iota x ph ) / x ]. ph )

  proof
    wph
    vx
    weu
    wph
    vx
    vz
    weq
    #
    wb
    #
    vx
    wal
    #
    vz
    wex
    wph
    vx
    wph
    vx
    cio
    #
    wsbc
    #
    wph
    vx
    vz
    df-eu
    @2
    @4
    vz
    @2
    wph
    vx
    vz
    wsb
    #
    @4
    @2
    @0
    wph
    wi
    #
    vx
    wal
    @5
    @1
    @6
    vx
    wph
    @0
    biimpr
    alimi
    wph
    vx
    vz
    sb2
    syl
    @2
    vz
    cv
    #
    @3
    wceq
    @5
    @4
    wb
    @2
    @3
    @7
    wph
    vx
    vz
    iotaval
    eqcomd
    wph
    vx
    vz
    @3
    dfsbcq2
    syl
    mpbid
    exlimiv
    sylbi
end
