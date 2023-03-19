include "cn.mm"
include "wss.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "nnuz.mm"
include "sseq2i.mm"
include "uzwo.mm"
include "sylanb.mm"

theorem nnwo
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( ( A C_ NN /\ A =/= (/) ) -> E. x e. A A. y e. A x <_ y )

  proof
    cA
    cn
    wss
    cA
    c1
    cuz
    cfv
    #
    wss
    cA
    c0
    wne
    vx
    cv
    vy
    cv
    cle
    wbr
    vy
    cA
    wral
    vx
    cA
    wrex
    cn
    @0
    cA
    nnuz
    sseq2i
    cA
    vx
    vy
    c1
    uzwo
    sylanb
end
