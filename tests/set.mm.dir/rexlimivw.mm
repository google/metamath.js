include "wi.mm"
include "cv.mm"
include "wcel.mm"
include "a1i.mm"
include "rexlimiv.mm"

theorem rexlimivw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume rexlimivw.1: |- ( ph -> ps )

  disjoint ps x
  assert |- ( E. x e. A ph -> ps )

  proof
    wph
    wps
    vx
    cA
    wph
    wps
    wi
    vx
    cv
    cA
    wcel
    rexlimivw.1
    a1i
    rexlimiv
end
