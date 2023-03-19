include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "csn.mm"
include "wfun.mm"
include "funsng.mm"
include "mp2an.mm"

theorem funsn
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  assume funsn.1: |- A e. _V
  assume funsn.2: |- B e. _V


  assert |- Fun { <. A , B >. }

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cop
    csn
    wfun
    funsn.1
    funsn.2
    cA
    cB
    cvv
    cvv
    funsng
    mp2an
end
