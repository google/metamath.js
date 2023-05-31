include "wn.mm"
include "ax-5.mm"
include "wal.mm"
include "spfw.mm"

theorem spw
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param vy: setvar y
  assume spw.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint ps x
  disjoint ph y
  assert |- ( A. x ph -> ph )

  proof
    wph
    wps
    vx
    vy
    wps
    wn
    vx
    ax-5
    wph
    vx
    wal
    vy
    ax-5
    wph
    wn
    vy
    ax-5
    spw.1
    spfw
end
