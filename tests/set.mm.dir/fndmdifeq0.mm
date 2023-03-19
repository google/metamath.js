include "wfn.mm"
include "wa.mm"
include "cdif.mm"
include "cdm.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "crab.mm"
include "fndmdif.mm"
include "eqeq1d.mm"
include "wral.mm"
include "eqfnfv.mm"
include "wn.mm"
include "rabeq0.mm"
include "nne.mm"
include "ralbii.mm"
include "bitri.mm"
include "syl6rbbr.mm"
include "bitrd.mm"

theorem fndmdifeq0
  let cA: class A
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F Fn A /\ G Fn A ) -> ( dom ( F \ G ) = (/) <-> F = G ) )

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
    cdif
    cdm
    #
    c0
    wceq
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
    #
    c0
    wceq
    #
    cF
    cG
    wceq
    #
    @0
    @1
    @6
    c0
    vx
    cA
    cF
    cG
    fndmdif
    eqeq1d
    @0
    @8
    @3
    @4
    wceq
    #
    vx
    cA
    wral
    #
    @7
    vx
    cA
    cF
    cG
    eqfnfv
    @7
    @5
    wn
    #
    vx
    cA
    wral
    @10
    @5
    vx
    cA
    rabeq0
    @11
    @9
    vx
    cA
    @3
    @4
    nne
    ralbii
    bitri
    syl6rbbr
    bitrd
end
