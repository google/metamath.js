include "wal.mm"
include "spimv1.mm"
include "alrimiv.mm"

theorem wl-cbv3vv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume wl-cbv3vv.nf: |- F/ x ps
  assume wl-cbv3vv.1: |- ( x = y -> ( ph -> ps ) )

  disjoint x y
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
    wl-cbv3vv.nf
    wl-cbv3vv.1
    spimv1
    alrimiv
end
