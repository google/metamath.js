include "nf5i.mm"
include "cbv3v.mm"

theorem cbv3hv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume cbv3hv.nf1: |- ( ph -> A. y ph )
  assume cbv3hv.nf2: |- ( ps -> A. x ps )
  assume cbv3hv.1: |- ( x = y -> ( ph -> ps ) )

  disjoint x y
  assert |- ( A. x ph -> A. y ps )

  proof
    wph
    wps
    vx
    vy
    wph
    vy
    cbv3hv.nf1
    nf5i
    wps
    vx
    cbv3hv.nf2
    nf5i
    cbv3hv.1
    cbv3v
end
