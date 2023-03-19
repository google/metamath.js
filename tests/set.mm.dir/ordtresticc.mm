include "cicc.mm"
include "co.mm"
include "iccssxr.mm"
include "cv.mm"
include "iccss2.mm"
include "ordtrestixx.mm"

theorem ordtresticc
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ordTop ` <_ ) |`t ( A [,] B ) ) = ( ordTop ` ( <_ i^i ( ( A [,] B ) X. ( A [,] B ) ) ) )

  proof
    vx
    vy
    cA
    cB
    cicc
    co
    cA
    cB
    iccssxr
    cA
    cB
    vx
    cv
    vy
    cv
    iccss2
    ordtrestixx
end
