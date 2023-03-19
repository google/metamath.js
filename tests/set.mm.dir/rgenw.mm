include "cv.mm"
include "wcel.mm"
include "a1i.mm"
include "rgen.mm"

theorem rgenw
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume rgenw.1: |- ph


  assert |- A. x e. A ph

  proof
    wph
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    rgenw.1
    a1i
    rgen
end
