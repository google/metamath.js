include "nfcv.mm"
include "rexcomf.mm"

theorem rexcom
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint B x
  disjoint A y
  assert |- ( E. x e. A E. y e. B ph <-> E. y e. B E. x e. A ph )

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
    rexcomf
end
