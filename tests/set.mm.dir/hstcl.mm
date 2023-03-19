include "chst.mm"
include "wcel.mm"
include "cch.mm"
include "chil.mm"
include "wf.mm"
include "cfv.mm"
include "cno.mm"
include "c1.mm"
include "wceq.mm"
include "cv.mm"
include "cort.mm"
include "wss.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "chj.mm"
include "cva.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "ishst.mm"
include "simp1bi.mm"
include "ffvelrnda.mm"

theorem hstcl
  let cA: class A
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cB: class B


  assert |- ( ( S e. CHStates /\ A e. CH ) -> ( S ` A ) e. ~H )

  proof
    cS
    chst
    wcel
    #
    cch
    chil
    cA
    cS
    @0
    cch
    chil
    cS
    wf
    chil
    cS
    cfv
    cno
    cfv
    c1
    wceq
    vx
    cv
    #
    vy
    cv
    #
    cort
    cfv
    wss
    @1
    cS
    cfv
    #
    @2
    cS
    cfv
    #
    csp
    co
    cc0
    wceq
    @1
    @2
    chj
    co
    cS
    cfv
    @3
    @4
    cva
    co
    wceq
    wa
    wi
    vy
    cch
    wral
    vx
    cch
    wral
    vx
    vy
    cS
    ishst
    simp1bi
    ffvelrnda
end
