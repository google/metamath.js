include "wrel.mm"
include "wceq.mm"
include "eqrelriv.mm"
include "mp2an.mm"

theorem eqrelriiv
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume eqreliiv.1: |- Rel A
  assume eqreliiv.2: |- Rel B
  assume eqreliiv.3: |- ( <. x , y >. e. A <-> <. x , y >. e. B )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- A = B

  proof
    cA
    wrel
    cB
    wrel
    cA
    cB
    wceq
    eqreliiv.1
    eqreliiv.2
    vx
    vy
    cA
    cB
    eqreliiv.3
    eqrelriv
    mp2an
end
