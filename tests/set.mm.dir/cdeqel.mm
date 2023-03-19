include "wcel.mm"
include "wb.mm"
include "weq.mm"
include "wceq.mm"
include "cdeqri.mm"
include "eleq12d.mm"
include "cdeqi.mm"

theorem cdeqel
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume cdeqeq.1: |- CondEq ( x = y -> A = B )
  assume cdeqeq.2: |- CondEq ( x = y -> C = D )


  assert |- CondEq ( x = y -> ( A e. C <-> B e. D ) )

  proof
    cA
    cC
    wcel
    cB
    cD
    wcel
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
    eleq12d
    cdeqi
end
