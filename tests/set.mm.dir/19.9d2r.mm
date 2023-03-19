include "nfv.mm"
include "19.9d2rf.mm"

theorem 19.9d2r
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume 19.9d2r.1: |- ( ph -> F/ x ps )
  assume 19.9d2r.2: |- ( ph -> F/ y ps )
  assume 19.9d2r.3: |- ( ph -> E. x e. A E. y e. B ps )

  disjoint ph y
  assert |- ( ph -> ps )

  proof
    wph
    wps
    vx
    vy
    cA
    cB
    wph
    vy
    nfv
    19.9d2r.1
    19.9d2r.2
    19.9d2r.3
    19.9d2rf
end
