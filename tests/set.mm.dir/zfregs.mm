include "cep.mm"
include "wfr.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "zfregfr.mm"
include "epfrs.mm"
include "mpan.mm"

theorem zfregs
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A =/= (/) -> E. x e. A ( x i^i A ) = (/) )

  proof
    cA
    cep
    wfr
    cA
    c0
    wne
    vx
    cv
    cA
    cin
    c0
    wceq
    vx
    cA
    wrex
    cA
    zfregfr
    vx
    cA
    epfrs
    mpan
end
