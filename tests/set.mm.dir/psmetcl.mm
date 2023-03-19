include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "cxr.mm"
include "wf.mm"
include "co.mm"
include "psmetf.mm"
include "fovrn.mm"
include "syl3an1.mm"

theorem psmetcl
  let cA: class A
  let cB: class B
  let cD: class D
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( ( D e. ( PsMet ` X ) /\ A e. X /\ B e. X ) -> ( A D B ) e. RR* )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    cX
    cX
    cxp
    cxr
    cD
    wf
    cA
    cX
    wcel
    cB
    cX
    wcel
    cA
    cB
    cD
    co
    cxr
    wcel
    cD
    cX
    psmetf
    cA
    cB
    cxr
    cX
    cX
    cD
    fovrn
    syl3an1
end
