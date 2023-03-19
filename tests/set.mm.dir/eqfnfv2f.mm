include "wfn.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "eqfnfv.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfeq.mm"
include "nfv.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "cbvral.mm"
include "syl6bb.mm"

theorem eqfnfv2f
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cG: class G
  let vz: setvar z
  assume eqfnfv2f.1: |- F/_ x F
  assume eqfnfv2f.2: |- F/_ x G

  disjoint A x
  disjoint x z
  disjoint A z
  disjoint F z
  disjoint G z
  assert |- ( ( F Fn A /\ G Fn A ) -> ( F = G <-> A. x e. A ( F ` x ) = ( G ` x ) ) )

  proof
    cF
    cA
    wfn
    cG
    cA
    wfn
    wa
    cF
    cG
    wceq
    vz
    cv
    #
    cF
    cfv
    #
    @0
    cG
    cfv
    #
    wceq
    #
    vz
    cA
    wral
    vx
    cv
    #
    cF
    cfv
    #
    @4
    cG
    cfv
    #
    wceq
    #
    vx
    cA
    wral
    vz
    cA
    cF
    cG
    eqfnfv
    @3
    @7
    vz
    vx
    cA
    vx
    @1
    @2
    vx
    @0
    cF
    eqfnfv2f.1
    vx
    @0
    nfcv
    #
    nffv
    vx
    @0
    cG
    eqfnfv2f.2
    @8
    nffv
    nfeq
    @7
    vz
    nfv
    @0
    @4
    wceq
    @1
    @5
    @2
    @6
    @0
    @4
    cF
    fveq2
    @0
    @4
    cG
    fveq2
    eqeq12d
    cbvral
    syl6bb
end
