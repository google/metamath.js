include "wi.mm"
include "wal.mm"
include "al2im.mm"
include "mpg.mm"

theorem al2imi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
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
