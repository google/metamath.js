include "wal.mm"
include "ax-5.mm"
include "wn.mm"
include "cbvalw.mm"

theorem cbvalvw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume cbvalvw.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint ps x
  disjoint ph y
  assert |- ( A. x ph <-> A. y ps )

  proof
    wph
    wps
    vx
    vy
    wph
    vx
    wal
    vy
    ax-5
    wps
    wn
    vx
    ax-5
    wps
    vy
    wal
    vx
    ax-5
    wph
    wn
    vy
    ax-5
    cbvalvw.1
    cbvalw
end
