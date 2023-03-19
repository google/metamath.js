include "wral.mm"
include "rgenw.mm"

theorem rgen2w
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume rgenw.1: |- ph


  assert |- A. x e. A A. y e. B ph

  proof
    wph
    vy
    cB
    wral
    vx
    cA
    wph
    vy
    cB
    rgenw.1
    rgenw
    rgenw
end
