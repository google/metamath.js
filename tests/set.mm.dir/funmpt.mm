include "cmpt.mm"
include "wfun.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "funopab4.mm"
include "df-mpt.mm"
include "funeqi.mm"
include "mpbir.mm"

theorem funmpt
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y


  assert |- Fun ( x e. A |-> B )

  proof
    vx
    cA
    cB
    cmpt
    #
    wfun
    vx
    cv
    cA
    wcel
    #
    vy
    cv
    cB
    wceq
    wa
    vx
    vy
    copab
    #
    wfun
    @1
    vx
    vy
    cB
    funopab4
    @0
    @2
    vx
    vy
    cA
    cB
    df-mpt
    funeqi
    mpbir
end
