include "wss.mm"
include "cv.mm"
include "csn.mm"
include "cmpt.mm"
include "cima.mm"
include "cuni.mm"
include "sneq.mm"
include "cbvmptv.mm"
include "eqcomi.mm"
include "mptsnunlem.mm"
include "eqtri.mm"
include "imaeq1i.mm"
include "unieqi.mm"
include "syl6eqr.mm"

theorem mptsnun
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let vy: setvar y
  assume mptsnun.f: |- F = ( x e. A |-> { x } )
  assume mptsnun.r: |- R = { u | E. x e. A u = { x } }

  disjoint A u
  disjoint A x
  disjoint u x
  disjoint B u
  disjoint B x
  disjoint A y
  disjoint x y
  assert |- ( B C_ A -> B = U. ( F " B ) )

  proof
    cB
    cA
    wss
    cB
    vy
    cA
    vy
    cv
    #
    csn
    #
    cmpt
    #
    cB
    cima
    #
    cuni
    cF
    cB
    cima
    #
    cuni
    vx
    vu
    cA
    cB
    cR
    @2
    vx
    cA
    vx
    cv
    #
    csn
    #
    cmpt
    #
    @2
    vx
    vy
    cA
    @6
    @1
    @5
    @0
    sneq
    cbvmptv
    #
    eqcomi
    mptsnun.r
    mptsnunlem
    @4
    @3
    cF
    @2
    cB
    cF
    @7
    @2
    mptsnun.f
    @8
    eqtri
    imaeq1i
    unieqi
    syl6eqr
end
