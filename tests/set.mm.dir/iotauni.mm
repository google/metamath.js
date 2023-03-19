include "weu.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "cio.mm"
include "cab.mm"
include "cuni.mm"
include "df-eu.mm"
include "iotaval.mm"
include "uniabio.mm"
include "eqtr4d.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem iotauni
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let wps: wff ps
  let vy: setvar y


  assert |- ( E! x ph -> ( iota x ph ) = U. { x | ph } )

  proof
    wph
    vx
    weu
    wph
    vx
    cv
    vz
    cv
    #
    wceq
    wb
    vx
    wal
    #
    vz
    wex
    wph
    vx
    cio
    #
    wph
    vx
    cab
    cuni
    #
    wceq
    #
    wph
    vx
    vz
    df-eu
    @1
    @4
    vz
    @1
    @2
    @0
    @3
    wph
    vx
    vz
    iotaval
    wph
    vx
    vz
    uniabio
    eqtr4d
    exlimiv
    sylbi
end
