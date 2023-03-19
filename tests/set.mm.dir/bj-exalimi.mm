include "wal.mm"
include "wex.mm"
include "com12.mm"
include "aleximi.mm"

theorem bj-exalimi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bj-exalimi.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( E. x ph -> ( A. x ps -> E. x ch ) )

  proof
    wps
    vx
    wal
    wph
    vx
    wex
    wch
    vx
    wex
    wps
    wph
    wch
    vx
    wph
    wps
    wch
    bj-exalimi.1
    com12
    aleximi
    com12
end
