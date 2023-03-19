include "nfcrii.mm"
include "cleqh.mm"

theorem cleqf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume cleqf.1: |- F/_ x A
  assume cleqf.2: |- F/_ x B


  assert |- ( A = B <-> A. x ( x e. A <-> x e. B ) )

  proof
    vx
    vy
    cA
    cB
    vx
    vy
    cA
    cleqf.1
    nfcrii
    vx
    vy
    cB
    cleqf.2
    nfcrii
    cleqh
end
