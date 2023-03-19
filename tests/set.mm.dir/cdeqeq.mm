include "wceq.mm"
include "wb.mm"
include "weq.mm"
include "cdeqri.mm"
include "eqeq12d.mm"
include "cdeqi.mm"

theorem cdeqeq
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume cdeqeq.1: |- CondEq ( x = y -> A = B )
  assume cdeqeq.2: |- CondEq ( x = y -> C = D )


  assert |- CondEq ( x = y -> ( A = C <-> B = D ) )

  proof
    cA
    cC
    wceq
    cB
    cD
    wceq
    wb
    vx
    vy
    vx
    vy
    weq
    cA
    cB
    cC
    cD
    cA
    cB
    wceq
    vx
    vy
    cdeqeq.1
    cdeqri
    cC
    cD
    wceq
    vx
    vy
    cdeqeq.2
    cdeqri
    eqeq12d
    cdeqi
end
