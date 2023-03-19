include "weu.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "cio.mm"
include "df-eu.mm"
include "sp.mm"
include "iotaval.mm"
include "eqeq2d.mm"
include "bitr4d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem iota1
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let wps: wff ps
  let vy: setvar y


  assert |- ( E! x ph -> ( ph <-> ( iota x ph ) = x ) )

  proof
    wph
    vx
    weu
    wph
    vx
    cv
    #
    vz
    cv
    #
    wceq
    #
    wb
    #
    vx
    wal
    #
    vz
    wex
    wph
    wph
    vx
    cio
    #
    @0
    wceq
    #
    wb
    #
    wph
    vx
    vz
    df-eu
    @4
    @7
    vz
    @4
    wph
    @0
    @5
    wceq
    #
    @6
    @4
    wph
    @2
    @8
    @3
    vx
    sp
    @4
    @5
    @1
    @0
    wph
    vx
    vz
    iotaval
    eqeq2d
    bitr4d
    @0
    @5
    eqcom
    syl6bb
    exlimiv
    sylbi
end
