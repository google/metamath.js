include "nf5i.mm"
include "equsalv.mm"

theorem bj-equsalhv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-equsalhv.nf: |- ( ps -> A. x ps )
  assume bj-equsalhv.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  assert |- ( A. x ( x = y -> ph ) <-> ps )

  proof
    wph
    wps
    vx
    vy
    wps
    vx
    bj-equsalhv.nf
    nf5i
    bj-equsalhv.1
    equsalv
end
