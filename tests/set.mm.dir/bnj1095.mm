include "wral.mm"
include "hbra1.mm"
include "hbxfrbi.mm"

theorem bnj1095
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume bnj1095.1: |- ( ph <-> A. x e. A ps )


  assert |- ( ph -> A. x ph )

  proof
    wph
    wps
    vx
    cA
    wral
    vx
    bnj1095.1
    wps
    vx
    cA
    hbra1
    hbxfrbi
end
