include "cv.mm"
include "wcel.mm"
include "ex.mm"
include "ralimia.mm"

theorem ralimiaa
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume ralimiaa.1: |- ( ( x e. A /\ ph ) -> ps )


  assert |- ( A. x e. A ph -> A. x e. A ps )

  proof
    wph
    wps
    vx
    cA
    vx
    cv
    cA
    wcel
    wph
    wps
    ralimiaa.1
    ex
    ralimia
end
