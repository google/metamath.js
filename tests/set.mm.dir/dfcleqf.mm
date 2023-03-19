include "cleqf.mm"

theorem dfcleqf
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume dfcleqf.1: |- F/_ x A
  assume dfcleqf.2: |- F/_ x B


  assert |- ( A = B <-> A. x ( x e. A <-> x e. B ) )

  proof
    vx
    cA
    cB
    dfcleqf.1
    dfcleqf.2
    cleqf
end
