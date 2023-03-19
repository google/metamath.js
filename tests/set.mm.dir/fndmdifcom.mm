include "wfn.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "crab.mm"
include "cdif.mm"
include "cdm.mm"
include "necom.mm"
include "rabbii.mm"
include "fndmdif.mm"
include "wceq.mm"
include "ancoms.mm"
include "3eqtr4a.mm"

theorem fndmdifcom
  let cA: class A
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F Fn A /\ G Fn A ) -> dom ( F \ G ) = dom ( G \ F ) )

  proof
    cF
    cA
    wfn
    #
    cG
    cA
    wfn
    #
    wa
    vx
    cv
    #
    cF
    cfv
    #
    @2
    cG
    cfv
    #
    wne
    #
    vx
    cA
    crab
    @4
    @3
    wne
    #
    vx
    cA
    crab
    #
    cF
    cG
    cdif
    cdm
    cG
    cF
    cdif
    cdm
    #
    @5
    @6
    vx
    cA
    @3
    @4
    necom
    rabbii
    vx
    cA
    cF
    cG
    fndmdif
    @1
    @0
    @8
    @7
    wceq
    vx
    cA
    cG
    cF
    fndmdif
    ancoms
    3eqtr4a
end
