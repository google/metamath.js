include "wcel.mm"
include "wfun.mm"
include "cima.mm"
include "wss.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "imaeq2.mm"
include "sseq2d.mm"
include "anbi2d.mm"
include "sseq2.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "vex.mm"
include "ssimaex.mm"
include "vtoclg.mm"
include "3impib.mm"

theorem ssimaexg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint F y
  assert |- ( ( A e. C /\ Fun F /\ B C_ ( F " A ) ) -> E. x ( x C_ A /\ B = ( F " x ) ) )

  proof
    cA
    cC
    wcel
    cF
    wfun
    #
    cB
    cF
    cA
    cima
    #
    wss
    #
    vx
    cv
    #
    cA
    wss
    #
    cB
    cF
    @3
    cima
    wceq
    #
    wa
    #
    vx
    wex
    #
    @0
    cB
    cF
    vy
    cv
    #
    cima
    #
    wss
    #
    wa
    #
    @3
    @8
    wss
    #
    @5
    wa
    #
    vx
    wex
    #
    wi
    @0
    @2
    wa
    #
    @7
    wi
    vy
    cA
    cC
    @8
    cA
    wceq
    #
    @11
    @15
    @14
    @7
    @16
    @10
    @2
    @0
    @16
    @9
    @1
    cB
    @8
    cA
    cF
    imaeq2
    sseq2d
    anbi2d
    @16
    @13
    @6
    vx
    @16
    @12
    @4
    @5
    @8
    cA
    @3
    sseq2
    anbi1d
    exbidv
    imbi12d
    vx
    @8
    cB
    cF
    vy
    vex
    ssimaex
    vtoclg
    3impib
end
