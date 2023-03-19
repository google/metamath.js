include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "cxp.mm"
include "wf.mm"
include "wfn.mm"
include "ffnov.mm"
include "simprbi.mm"
include "ax-mp.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "mpi.mm"

theorem fovcl
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  assume fovcl.1: |- F : ( R X. S ) --> C


  assert |- ( ( A e. R /\ B e. S ) -> ( A F B ) e. C )

  proof
    cA
    cR
    wcel
    cB
    cS
    wcel
    wa
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    cC
    wcel
    #
    vy
    cS
    wral
    vx
    cR
    wral
    #
    cA
    cB
    cF
    co
    #
    cC
    wcel
    #
    cR
    cS
    cxp
    #
    cC
    cF
    wf
    #
    @4
    fovcl.1
    @8
    cF
    @7
    wfn
    @4
    vx
    vy
    cR
    cS
    cC
    cF
    ffnov
    simprbi
    ax-mp
    @3
    @6
    cA
    @1
    cF
    co
    #
    cC
    wcel
    vx
    vy
    cA
    cB
    cR
    cS
    @0
    cA
    wceq
    @2
    @9
    cC
    @0
    cA
    @1
    cF
    oveq1
    eleq1d
    @1
    cB
    wceq
    @9
    @5
    cC
    @1
    cB
    cA
    cF
    oveq2
    eleq1d
    rspc2v
    mpi
end
