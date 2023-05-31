include "weq.mm"
include "wn.mm"
include "wal.mm"
include "wi.mm"
include "ax6v.mm"
include "spimfw.mm"
include "ax-mp.mm"

theorem spimw
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param vy: setvar y
  assume spimw.1: |- ( -. ps -> A. x -. ps )
  assume spimw.2: |- ( x = y -> ( ph -> ps ) )

  disjoint x y
  assert |- ( A. x ph -> ps )

  proof
    vx
    vy
    weq
    wn
    vx
    wal
    wn
    wph
    vx
    wal
    wps
    wi
    vx
    vy
    ax6v
    wph
    wps
    vx
    vy
    spimw.1
    spimw.2
    spimfw
    ax-mp
end
