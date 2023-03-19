include "nfcv.mm"
include "ralcomf.mm"

theorem ralcom
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint B x
  disjoint A y
  assert |- ( A. x e. A A. y e. B ph <-> A. y e. B A. x e. A ph )

  proof
    wph
    vx
    vy
    cA
    cB
    vy
    cA
    nfcv
    vx
    cB
    nfcv
    ralcomf
end
