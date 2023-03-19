include "wal.mm"
include "alimdv.mm"

theorem 2alimdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume 2alimdv.1: |- ( ph -> ( ps -> ch ) )

  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( A. x A. y ps -> A. x A. y ch ) )

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
    2alimdv.1
    alimdv
    alimdv
end
