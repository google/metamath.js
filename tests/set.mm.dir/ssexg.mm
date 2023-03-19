include "wcel.mm"
include "wss.mm"
include "cvv.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "sseq2.mm"
include "imbi1d.mm"
include "vex.mm"
include "ssex.mm"
include "vtoclg.mm"
include "impcom.mm"

theorem ssexg
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( A C_ B /\ B e. C ) -> A e. _V )

  proof
    cB
    cC
    wcel
    cA
    cB
    wss
    #
    cA
    cvv
    wcel
    #
    cA
    vx
    cv
    #
    wss
    #
    @1
    wi
    @0
    @1
    wi
    vx
    cB
    cC
    @2
    cB
    wceq
    @3
    @0
    @1
    @2
    cB
    cA
    sseq2
    imbi1d
    cA
    @2
    vx
    vex
    ssex
    vtoclg
    impcom
end
