include "wal.mm"
include "spimw.mm"
include "alrimih.mm"

theorem cbvaliw
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param vy: setvar y
  assume cbvaliw.1: |- ( A. x ph -> A. y A. x ph )
  assume cbvaliw.2: |- ( -. ps -> A. x -. ps )
  assume cbvaliw.3: |- ( x = y -> ( ph -> ps ) )

  disjoint x y
  assert |- ( A. x ph -> A. y ps )

  proof
    wph
    vx
    wal
    wps
    vy
    cbvaliw.1
    wph
    wps
    vx
    vy
    cbvaliw.2
    cbvaliw.3
    spimw
    alrimih
end
