include "chil.mm"
include "wss.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "cun.mm"
include "cort.mm"
include "cfv.mm"
include "cv.mm"
include "cch.mm"
include "crab.mm"
include "cint.mm"
include "sshjval.mm"
include "wceq.mm"
include "unss.mm"
include "ococin.mm"
include "sylbi.mm"
include "eqtrd.mm"

theorem sshjval2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  assert |- ( ( A C_ ~H /\ B C_ ~H ) -> ( A vH B ) = |^| { x e. CH | ( A u. B ) C_ x } )

  proof
    cA
    chil
    wss
    cB
    chil
    wss
    wa
    #
    cA
    cB
    chj
    co
    cA
    cB
    cun
    #
    cort
    cfv
    cort
    cfv
    #
    @1
    vx
    cv
    wss
    vx
    cch
    crab
    cint
    #
    cA
    cB
    sshjval
    @0
    @1
    chil
    wss
    @2
    @3
    wceq
    cA
    cB
    chil
    unss
    vx
    @1
    ococin
    sylbi
    eqtrd
end
