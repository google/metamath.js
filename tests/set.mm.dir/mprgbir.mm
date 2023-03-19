include "wral.mm"
include "rgen.mm"
include "mpbir.mm"

theorem mprgbir
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume mprgbir.1: |- ( ph <-> A. x e. A ps )
  assume mprgbir.2: |- ( x e. A -> ps )


  assert |- ph

  proof
    wph
    wps
    vx
    cA
    wral
    wps
    vx
    cA
    mprgbir.2
    rgen
    mprgbir.1
    mpbir
end
