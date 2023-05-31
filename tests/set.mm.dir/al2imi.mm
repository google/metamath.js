include "wi.mm"
include "wal.mm"
include "al2im.mm"
include "mpg.mm"

theorem al2imi
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  assume al2imi.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( A. x ph -> ( A. x ps -> A. x ch ) )

  proof
    wph
    wps
    wch
    wi
    wi
    wph
    vx
    wal
    wps
    vx
    wal
    wch
    vx
    wal
    wi
    wi
    vx
    wph
    wps
    wch
    vx
    al2im
    al2imi.1
    mpg
end
