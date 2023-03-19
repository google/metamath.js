include "wex.mm"
include "weq.mm"
include "cbvexdva.mm"
include "cbvexv.mm"

theorem cbvex2v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume cbval2v.1: |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) )

  disjoint w z
  disjoint ph z
  disjoint ph w
  disjoint x y
  disjoint ps x
  disjoint ps y
  disjoint w x
  disjoint y z
  assert |- ( E. x E. y ph <-> E. z E. w ps )

  proof
    wph
    vy
    wex
    wps
    vw
    wex
    vx
    vz
    vx
    vz
    weq
    wph
    wps
    vy
    vw
    cbval2v.1
    cbvexdva
    cbvexv
end
