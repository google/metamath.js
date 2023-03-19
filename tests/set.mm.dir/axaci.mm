include "wac.mm"
include "wal.mm"
include "axac3.mm"
include "mpbi.mm"
include "spi.mm"

theorem axaci
  let wph: wff ph
  let vx: setvar x
  assume axaci.1: |- ( CHOICE <-> A. x ph )


  assert |- ph

  proof
    wph
    vx
    wac
    wph
    vx
    wal
    axac3
    axaci.1
    mpbi
    spi
end
