include "wfn.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "crab.mm"
include "cin.mm"
include "cdm.mm"
include "wral.mm"
include "eqfnfv.mm"
include "eqcom.mm"
include "rabid2.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "fndmin.mm"
include "eqeq1d.mm"
include "bitr4d.mm"

theorem fneqeql
  let cA: class A
  let cF: class F
  let cG: class G
  let vx: setvar x


  assert |- ( ( F Fn A /\ G Fn A ) -> ( F = G <-> dom ( F i^i G ) = A ) )

  proof
    cF
    cA
    wfn
    cG
    cA
    wfn
    wa
    #
    cF
    cG
    wceq
    #
    vx
    cv
    #
    cF
    cfv
    @2
    cG
    cfv
    wceq
    #
    vx
    cA
    crab
    #
    cA
    wceq
    #
    cF
    cG
    cin
    cdm
    #
    cA
    wceq
    @0
    @1
    @3
    vx
    cA
    wral
    #
    @5
    vx
    cA
    cF
    cG
    eqfnfv
    @5
    cA
    @4
    wceq
    @7
    @4
    cA
    eqcom
    @3
    vx
    cA
    rabid2
    bitri
    syl6bbr
    @0
    @6
    @4
    cA
    vx
    cA
    cF
    cG
    fndmin
    eqeq1d
    bitr4d
end
