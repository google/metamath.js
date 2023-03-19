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
include "ifeq1.mm"
include "mpteq2dv.mm"
include "recseq.mm"
include "syl.mm"
include "df-rdg.mm"
include "3eqtr4g.mm"

theorem rdgeq2
  let cA: class A
  let cB: class B
  let cF: class F
  let vg: setvar g
  let cG: class G


  assert |- ( A = B -> rec ( F , A ) = rec ( F , B ) )

  proof
    cA
    cB
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
    @1
    crn
    cuni
    @3
    cuni
    @1
    cfv
    cF
    cfv
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
    cB
    @4
    cif
    #
    cmpt
    #
    crecs
    #
    cF
    cA
    crdg
    cF
    cB
    crdg
    @0
    @6
    @9
    wceq
    @7
    @10
    wceq
    @0
    vg
    cvv
    @5
    @8
    @2
    cA
    cB
    @4
    ifeq1
    mpteq2dv
    @6
    @9
    recseq
    syl
    vg
    cF
    cA
    df-rdg
    vg
    cF
    cB
    df-rdg
    3eqtr4g
end
