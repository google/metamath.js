include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "nfcri.mm"
include "19.21.mm"
include "r2allem.mm"

theorem r2alf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume r2alf.1: |- F/_ y A

  disjoint x y
  assert |- ( A. x e. A A. y e. B ph <-> A. x A. y ( ( x e. A /\ y e. B ) -> ph ) )

  proof
    wph
    vx
    vy
    cA
    cB
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    wph
    wi
    vy
    vy
    vx
    cA
    r2alf.1
    nfcri
    19.21
    r2allem
end
