include "cpcmp.mm"
include "wcel.mm"
include "cvv.mm"
include "clocfin.mm"
include "cfv.mm"
include "ccref.mm"
include "elex.mm"
include "cv.mm"
include "wceq.mm"
include "id.mm"
include "fveq2.mm"
include "crefeq.mm"
include "syl.mm"
include "eleq12d.mm"
include "df-pcmp.mm"
include "elab2g.mm"
include "pm5.21nii.mm"

theorem ispcmp
  let cJ: class J
  let vj: setvar j


  assert |- ( J e. Paracomp <-> J e. CovHasRef ( LocFin ` J ) )

  proof
    cJ
    cpcmp
    wcel
    cJ
    cvv
    wcel
    cJ
    cJ
    clocfin
    cfv
    #
    ccref
    #
    wcel
    #
    cJ
    cpcmp
    elex
    cJ
    @1
    elex
    vj
    cv
    #
    @3
    clocfin
    cfv
    #
    ccref
    #
    wcel
    @2
    vj
    cJ
    cpcmp
    cvv
    @3
    cJ
    wceq
    #
    @3
    cJ
    @5
    @1
    @6
    id
    @6
    @4
    @0
    wceq
    @5
    @1
    wceq
    @3
    cJ
    clocfin
    fveq2
    @4
    @0
    crefeq
    syl
    eleq12d
    vj
    df-pcmp
    elab2g
    pm5.21nii
end
