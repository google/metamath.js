include "crdg.mm"
include "cvv.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "cdm.mm"
include "wlim.mm"
include "crn.mm"
include "cuni.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "crecs.mm"
include "df-rdg.mm"
include "nfcv.mm"
include "nfv.mm"
include "nffv.mm"
include "nfif.mm"
include "nfmpt.mm"
include "nfrecs.mm"
include "nfcxfr.mm"

theorem nfrdg
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vg: setvar g
  assume nfrdg.1: |- F/_ x F
  assume nfrdg.2: |- F/_ x A


  assert |- F/_ x rec ( F , A )

  proof
    vx
    cF
    cA
    crdg
    vg
    cvv
    vg
    cv
    #
    c0
    wceq
    #
    cA
    @0
    cdm
    #
    wlim
    #
    @0
    crn
    cuni
    #
    @2
    cuni
    @0
    cfv
    #
    cF
    cfv
    #
    cif
    #
    cif
    #
    cmpt
    #
    crecs
    vg
    cF
    cA
    df-rdg
    vx
    @9
    vx
    vg
    cvv
    @8
    vx
    cvv
    nfcv
    @1
    vx
    cA
    @7
    @1
    vx
    nfv
    nfrdg.2
    @3
    vx
    @4
    @6
    @3
    vx
    nfv
    vx
    @4
    nfcv
    vx
    @5
    cF
    nfrdg.1
    vx
    @5
    nfcv
    nffv
    nfif
    nfif
    nfmpt
    nfrecs
    nfcxfr
end
