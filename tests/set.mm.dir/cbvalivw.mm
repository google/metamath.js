include "wal.mm"
include "spimvw.mm"
include "alrimiv.mm"

theorem cbvalivw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume cbvalivw.1: |- ( x = y -> ( ph -> ps ) )

  disjoint x y
  disjoint ps x
  disjoint ph y
  assert |- ( A. x ph -> A. y ps )

  proof
    wph
    vx
    wal
    wps
    vy
    wph
    wps
    vx
    vy
    cbvalivw.1
    spimvw
    alrimiv
end
