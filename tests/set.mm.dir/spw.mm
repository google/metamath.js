include "wn.mm"
include "ax-5.mm"
include "wal.mm"
include "spfw.mm"

theorem spw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
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
