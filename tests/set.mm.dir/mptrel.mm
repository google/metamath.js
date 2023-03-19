include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "cmpt.mm"
include "df-mpt.mm"
include "relopabi.mm"

theorem mptrel
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y


  assert |- Rel ( x e. A |-> B )

  proof
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wceq
    wa
    vx
    vy
    vx
    cA
    cB
    cmpt
    vx
    vy
    cA
    cB
    df-mpt
    relopabi
end
