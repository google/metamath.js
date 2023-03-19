include "rexabsle.mm"

theorem rexabsle2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume rexabsle2.1: |- F/ x ph
  assume rexabsle2.2: |- ( ( ph /\ x e. A ) -> B e. RR )

  disjoint A y
  disjoint B y
  disjoint x y
  assert |- ( ph -> ( E. y e. RR A. x e. A ( abs ` B ) <_ y <-> ( E. y e. RR A. x e. A B <_ y /\ E. y e. RR A. x e. A y <_ B ) ) )

  proof
    wph
    vx
    vy
    vy
    vy
    cA
    cB
    rexabsle2.1
    rexabsle2.2
    rexabsle
end
