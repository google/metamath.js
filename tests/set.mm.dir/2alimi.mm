include "wal.mm"
include "alimi.mm"

theorem 2alimi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume alimi.1: |- ( ph -> ps )


  assert |- ( A. x A. y ph -> A. x A. y ps )

  proof
    wph
    vy
    wal
    wps
    vy
    wal
    vx
    wph
    wps
    vy
    alimi.1
    alimi
    alimi
end
