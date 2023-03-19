include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "caov.mm"
include "wral.mm"
include "cxp.mm"
include "wf.mm"
include "wfn.mm"
include "ffnaov.mm"
include "simprbi.mm"
include "ax-mp.mm"
include "wceq.mm"
include "eqidd.mm"
include "id.mm"
include "aoveq123d.mm"
include "eleq1d.mm"
include "rspc2v.mm"
include "mpi.mm"

theorem faovcl
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume faovcl.1: |- F : ( R X. S ) --> C


  assert |- ( ( A e. R /\ B e. S ) -> (( A F B )) e. C )

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
    caov
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
    caov
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
    faovcl.1
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
    ffnaov
    simprbi
    ax-mp
    @3
    @6
    cA
    @1
    cF
    caov
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
    #
    @2
    @9
    cC
    @10
    @0
    cA
    @1
    @1
    cF
    cF
    @10
    cF
    eqidd
    @10
    id
    @10
    @1
    eqidd
    aoveq123d
    eleq1d
    @1
    cB
    wceq
    #
    @9
    @5
    cC
    @11
    cA
    cA
    @1
    cB
    cF
    cF
    @11
    cF
    eqidd
    @11
    cA
    eqidd
    @11
    id
    aoveq123d
    eleq1d
    rspc2v
    mpi
end
