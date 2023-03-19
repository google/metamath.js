include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "cio.mm"
include "weu.mm"
include "cvv.mm"
include "wcel.mm"
include "iotaval.mm"
include "eqcomd.mm"
include "eximi.mm"
include "df-eu.mm"
include "isset.mm"
include "3imtr4i.mm"

theorem iotaexeu
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E! x ph -> ( iota x ph ) e. _V )

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
    @0
    wph
    vx
    cio
    #
    wceq
    #
    vy
    wex
    wph
    vx
    weu
    @2
    cvv
    wcel
    @1
    @3
    vy
    @1
    @2
    @0
    wph
    vx
    vy
    iotaval
    eqcomd
    eximi
    wph
    vx
    vy
    df-eu
    vy
    @2
    isset
    3imtr4i
end
