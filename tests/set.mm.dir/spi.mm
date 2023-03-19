include "wal.mm"
include "sp.mm"
include "ax-mp.mm"

theorem spi
  let wph: wff ph
  let vx: setvar x
  assume spi.1: |- A. x ph


  assert |- ph

  proof
    wph
    vx
    wal
    wph
    spi.1
    wph
    vx
    sp
    ax-mp
end
