include "wral.mm"
include "ralimi.mm"

theorem 2ralimi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume ralimi.1: |- ( ph -> ps )


  assert |- ( A. x e. A A. y e. B ph -> A. x e. A A. y e. B ps )

  proof
    wph
    vy
    cB
    wral
    wps
    vy
    cB
    wral
    vx
    cA
    wph
    wps
    vy
    cB
    ralimi.1
    ralimi
    ralimi
end
