include "wral.mm"
include "2ralbii.mm"
include "ralbii.mm"

theorem 3ralbii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  assume 3ralbii.1: |- ( ph <-> ps )


  assert |- ( A. x e. A A. y e. B A. z e. C ph <-> A. x e. A A. y e. B A. z e. C ps )

  proof
    wph
    vz
    cC
    wral
    vy
    cB
    wral
    wps
    vz
    cC
    wral
    vy
    cB
    wral
    vx
    cA
    wph
    wps
    vy
    vz
    cB
    cC
    3ralbii.1
    2ralbii
    ralbii
end
