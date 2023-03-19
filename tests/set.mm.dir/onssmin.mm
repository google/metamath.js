include "con0.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cint.mm"
include "wcel.mm"
include "cv.mm"
include "wral.mm"
include "wrex.mm"
include "onint.mm"
include "intss1.mm"
include "rgen.mm"
include "wceq.mm"
include "sseq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "sylancl.mm"

theorem onssmin
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( ( A C_ On /\ A =/= (/) ) -> E. x e. A A. y e. A x C_ y )

  proof
    cA
    con0
    wss
    cA
    c0
    wne
    wa
    cA
    cint
    #
    cA
    wcel
    @0
    vy
    cv
    #
    wss
    #
    vy
    cA
    wral
    #
    vx
    cv
    #
    @1
    wss
    #
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    cA
    onint
    @2
    vy
    cA
    @1
    cA
    intss1
    rgen
    @6
    @3
    vx
    @0
    cA
    @4
    @0
    wceq
    @5
    @2
    vy
    cA
    @4
    @0
    @1
    sseq1
    ralbidv
    rspcev
    sylancl
end
