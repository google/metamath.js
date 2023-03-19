include "wa.mm"
include "wal.mm"
include "19.28.mm"
include "albii.mm"
include "nfal.mm"
include "19.27.mm"
include "bitri.mm"

theorem aaan
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume aaan.1: |- F/ y ph
  assume aaan.2: |- F/ x ps


  assert |- ( A. x A. y ( ph /\ ps ) <-> ( A. x ph /\ A. y ps ) )

  proof
    wph
    wps
    wa
    vy
    wal
    #
    vx
    wal
    wph
    wps
    vy
    wal
    #
    wa
    #
    vx
    wal
    wph
    vx
    wal
    @1
    wa
    @0
    @2
    vx
    wph
    wps
    vy
    aaan.1
    19.28
    albii
    wph
    @1
    vx
    wps
    vx
    vy
    aaan.2
    nfal
    19.27
    bitri
end
