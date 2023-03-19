include "wal.mm"
include "albidv.mm"

theorem 2albidv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume 2albidv.1: |- ( ph -> ( ps <-> ch ) )

  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( A. x A. y ps <-> A. x A. y ch ) )

  proof
    wph
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
    2albidv.1
    albidv
    albidv
end
