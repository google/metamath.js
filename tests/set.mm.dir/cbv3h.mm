include "nf5i.mm"
include "cbv3.mm"

theorem cbv3h
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume cbv3h.1: |- ( ph -> A. y ph )
  assume cbv3h.2: |- ( ps -> A. x ps )
  assume cbv3h.3: |- ( x = y -> ( ph -> ps ) )


  assert |- ( A. x ph -> A. y ps )

  proof
    wph
    wps
    vx
    vy
    wph
    vy
    cbv3h.1
    nf5i
    wps
    vx
    cbv3h.2
    nf5i
    cbv3h.3
    cbv3
end
