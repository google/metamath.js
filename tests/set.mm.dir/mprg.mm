include "wral.mm"
include "rgen.mm"
include "ax-mp.mm"

theorem mprg
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume mprg.1: |- ( A. x e. A ph -> ps )
  assume mprg.2: |- ( x e. A -> ph )


  assert |- ps

  proof
    wph
    vx
    cA
    wral
    wps
    wph
    vx
    cA
    mprg.2
    rgen
    mprg.1
    ax-mp
end
