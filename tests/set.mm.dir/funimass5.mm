include "wfun.mm"
include "cdm.mm"
include "wss.mm"
include "wa.mm"
include "cima.mm"
include "ccnv.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "funimass3.mm"
include "funimass4.mm"
include "bitr3d.mm"

theorem funimass5
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint F x
  disjoint A x
  disjoint B x
  assert |- ( ( Fun F /\ A C_ dom F ) -> ( A C_ ( `' F " B ) <-> A. x e. A ( F ` x ) e. B ) )

  proof
    cF
    wfun
    cA
    cF
    cdm
    wss
    wa
    cF
    cA
    cima
    cB
    wss
    cA
    cF
    ccnv
    cB
    cima
    wss
    vx
    cv
    cF
    cfv
    cB
    wcel
    vx
    cA
    wral
    cA
    cB
    cF
    funimass3
    vx
    cA
    cB
    cF
    funimass4
    bitr3d
end
