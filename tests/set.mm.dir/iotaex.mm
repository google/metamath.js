include "weu.mm"
include "cio.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "iotaval.mm"
include "eqcomd.mm"
include "eximi.mm"
include "df-eu.mm"
include "isset.mm"
include "3imtr4i.mm"
include "wn.mm"
include "c0.mm"
include "iotanul.mm"
include "0ex.mm"
include "syl6eqel.mm"
include "pm2.61i.mm"

theorem iotaex
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let wps: wff ps
  let vy: setvar y


  assert |- ( iota x ph ) e. _V

  proof
    wph
    vx
    weu
    #
    wph
    vx
    cio
    #
    cvv
    wcel
    #
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
    @3
    @1
    wceq
    #
    vz
    wex
    @0
    @2
    @4
    @5
    vz
    @4
    @1
    @3
    wph
    vx
    vz
    iotaval
    eqcomd
    eximi
    wph
    vx
    vz
    df-eu
    vz
    @1
    isset
    3imtr4i
    @0
    wn
    @1
    c0
    cvv
    wph
    vx
    iotanul
    0ex
    syl6eqel
    pm2.61i
end
