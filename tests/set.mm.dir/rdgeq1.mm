include "wceq.mm"
include "cvv.mm"
include "cv.mm"
include "c0.mm"
include "cdm.mm"
include "wlim.mm"
include "crn.mm"
include "cuni.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "crecs.mm"
include "crdg.mm"
include "fveq1.mm"
include "ifeq2d.mm"
include "mpteq2dv.mm"
include "recseq.mm"
include "syl.mm"
include "df-rdg.mm"
include "3eqtr4g.mm"

theorem rdgeq1
  let cA: class A
  let cF: class F
  let cG: class G
  let vg: setvar g
  let cB: class B


  assert |- ( F = G -> rec ( F , A ) = rec ( G , A ) )

  proof
    cF
    cG
    wceq
    #
    vg
    cvv
    vg
    cv
    #
    c0
    wceq
    #
    cA
    @1
    cdm
    #
    wlim
    #
    @1
    crn
    cuni
    #
    @3
    cuni
    @1
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
    #
    vg
    cvv
    @2
    cA
    @4
    @5
    @6
    cG
    cfv
    #
    cif
    #
    cif
    #
    cmpt
    #
    crecs
    #
    cF
    cA
    crdg
    cG
    cA
    crdg
    @0
    @10
    @15
    wceq
    @11
    @16
    wceq
    @0
    vg
    cvv
    @9
    @14
    @0
    @2
    @8
    @13
    cA
    @0
    @4
    @7
    @12
    @5
    @6
    cF
    cG
    fveq1
    ifeq2d
    ifeq2d
    mpteq2dv
    @10
    @15
    recseq
    syl
    vg
    cF
    cA
    df-rdg
    vg
    cG
    cA
    df-rdg
    3eqtr4g
end
