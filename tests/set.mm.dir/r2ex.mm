include "wn.mm"
include "r2al.mm"
include "r2exlem.mm"

theorem r2ex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint A y
  assert |- ( E. x e. A E. y e. B ph <-> E. x E. y ( ( x e. A /\ y e. B ) /\ ph ) )

  proof
    wph
    vx
    vy
    cA
    cB
    wph
    wn
    vx
    vy
    cA
    cB
    r2al
    r2exlem
end
