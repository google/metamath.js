include "wn.mm"
include "r2alf.mm"
include "r2exlem.mm"

theorem r2exf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume r2exf.1: |- F/_ y A

  disjoint x y
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
    r2exf.1
    r2alf
    r2exlem
end
