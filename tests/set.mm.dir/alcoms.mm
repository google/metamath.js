include "wal.mm"
include "ax-11.mm"
include "syl.mm"

theorem alcoms
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume alcoms.1: |- ( A. x A. y ph -> ps )


  assert |- ( A. y A. x ph -> ps )

  proof
    wph
    vx
    wal
    vy
    wal
    wph
    vy
    wal
    vx
    wal
    wps
    wph
    vy
    vx
    ax-11
    alcoms.1
    syl
end
