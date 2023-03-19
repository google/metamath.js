include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "wsbc.mm"
include "cio.mm"
include "19.8a.mm"
include "weu.mm"
include "wi.mm"
include "df-eu.mm"
include "iotavalb.mm"
include "dfsbcq.mm"
include "eqcoms.mm"
include "syl6bi.mm"
include "sylbir.mm"
include "mpcom.mm"

theorem iotavalsb
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint ph y
  assert |- ( A. x ( ph <-> x = y ) -> ( [. y / z ]. ps <-> [. ( iota x ph ) / z ]. ps ) )

  proof
    wph
    vx
    cv
    vy
    cv
    #
    wceq
    wb
    vx
    wal
    #
    vy
    wex
    #
    @1
    wps
    vz
    @0
    wsbc
    wps
    vz
    wph
    vx
    cio
    #
    wsbc
    wb
    #
    @1
    vy
    19.8a
    @2
    wph
    vx
    weu
    #
    @1
    @4
    wi
    wph
    vx
    vy
    df-eu
    @5
    @1
    @3
    @0
    wceq
    @4
    wph
    vx
    vy
    iotavalb
    @4
    @0
    @3
    wps
    vz
    @0
    @3
    dfsbcq
    eqcoms
    syl6bi
    sylbir
    mpcom
end
