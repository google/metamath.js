include "wal.mm"
include "al2imi.mm"

theorem 2al2imi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume 2al2imi.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( A. x A. y ph -> ( A. x A. y ps -> A. x A. y ch ) )

  proof
    wph
    vy
    wal
    wps
    vy
    wal
    wch
    vy
    wal
    vx
    wph
    wps
    wch
    vy
    2al2imi.1
    al2imi
    al2imi
end
