include "wrel.mm"
include "c0.mm"
include "wceq.mm"
include "cdm.mm"
include "crn.mm"
include "reldm0.mm"
include "dm0rn0.mm"
include "syl6bb.mm"

theorem relrn0
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( Rel A -> ( A = (/) <-> ran A = (/) ) )

  proof
    cA
    wrel
    cA
    c0
    wceq
    cA
    cdm
    c0
    wceq
    cA
    crn
    c0
    wceq
    cA
    reldm0
    cA
    dm0rn0
    syl6bb
end
