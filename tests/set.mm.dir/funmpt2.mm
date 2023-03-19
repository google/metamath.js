include "wfun.mm"
include "cmpt.mm"
include "funmpt.mm"
include "funeqi.mm"
include "mpbir.mm"

theorem funmpt2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume funmpt2.1: |- F = ( x e. A |-> B )


  assert |- Fun F

  proof
    cF
    wfun
    vx
    cA
    cB
    cmpt
    #
    wfun
    vx
    cA
    cB
    funmpt
    cF
    @0
    funmpt2.1
    funeqi
    mpbir
end
