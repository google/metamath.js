include "wreu.mm"
include "crab.mm"
include "crio.mm"
include "ssrab2.mm"
include "riotacl2.mm"
include "sseldi.mm"

theorem riotacl
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( E! x e. A ph -> ( iota_ x e. A ph ) e. A )

  proof
    wph
    vx
    cA
    wreu
    wph
    vx
    cA
    crab
    cA
    wph
    vx
    cA
    crio
    wph
    vx
    cA
    ssrab2
    wph
    vx
    cA
    riotacl2
    sseldi
end
