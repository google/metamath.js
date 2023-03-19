include "con0.mm"
include "wcel.mm"
include "cv.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wss.mm"
include "wa.mm"
include "oaword1.mm"
include "sseq2.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "imp.mm"

theorem oawordexr
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ( A e. On /\ E. x e. On ( A +o x ) = B ) -> A C_ B )

  proof
    cA
    con0
    wcel
    #
    cA
    vx
    cv
    #
    coa
    co
    #
    cB
    wceq
    #
    vx
    con0
    wrex
    cA
    cB
    wss
    #
    @0
    @3
    @4
    vx
    con0
    @0
    @1
    con0
    wcel
    wa
    cA
    @2
    wss
    @3
    @4
    cA
    @1
    oaword1
    @2
    cB
    cA
    sseq2
    syl5ibcom
    rexlimdva
    imp
end
