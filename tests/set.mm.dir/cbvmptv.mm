include "nfcv.mm"
include "cbvmpt.mm"

theorem cbvmptv
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume cbvmptv.1: |- ( x = y -> B = C )

  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C x
  assert |- ( x e. A |-> B ) = ( y e. A |-> C )

  proof
    vx
    vy
    cA
    cB
    cC
    vy
    cB
    nfcv
    vx
    cC
    nfcv
    cbvmptv.1
    cbvmpt
end
