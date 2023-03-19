include "wal.mm"
include "wi.mm"
include "wn.mm"
include "hbntg.mm"
include "mpg.mm"

theorem hbng
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume hbg.1: |- ( ph -> A. x ps )


  assert |- ( -. ps -> A. x -. ph )

  proof
    wph
    wps
    vx
    wal
    wi
    wps
    wn
    wph
    wn
    vx
    wal
    wi
    vx
    wph
    wps
    vx
    hbntg
    hbg.1
    mpg
end
