include "wral.mm"
include "nfcv.mm"
include "nfra1.mm"
include "nfral.mm"

theorem nfra2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint A y
  assert |- F/ y A. x e. A A. y e. B ph

  proof
    wph
    vy
    cB
    wral
    vy
    vx
    cA
    vy
    cA
    nfcv
    wph
    vy
    cB
    nfra1
    nfral
end
