include "nf5i.mm"
include "equsexv.mm"

theorem equsexhv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume equsalhw.1: |- ( ps -> A. x ps )
  assume equsalhw.2: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  assert |- ( E. x ( x = y /\ ph ) <-> ps )

  proof
    wph
    wps
    vx
    vy
    wps
    vx
    equsalhw.1
    nf5i
    equsalhw.2
    equsexv
end
