include "cmre.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "cvv.mm"
include "wrex.mm"
include "wfn.mm"
include "wb.mm"
include "fnmre.mm"
include "fnunirn.mm"
include "ax-mp.mm"
include "mreuni.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "ibir.mm"
include "rexlimivw.mm"
include "sylbi.mm"
include "fvssunirn.mm"
include "sseli.mm"
include "impbii.mm"

theorem mreunirn
  let cC: class C
  let vc: setvar c
  let vs: setvar s
  let vx: setvar x
  let cX: class X
  let cS: class S
  let cI: class I
  let vy: setvar y


  assert |- ( C e. U. ran Moore <-> C e. ( Moore ` U. C ) )

  proof
    cC
    cmre
    crn
    cuni
    #
    wcel
    #
    cC
    cC
    cuni
    #
    cmre
    cfv
    #
    wcel
    #
    @1
    cC
    vx
    cv
    #
    cmre
    cfv
    #
    wcel
    #
    vx
    cvv
    wrex
    #
    @4
    cmre
    cvv
    wfn
    @1
    @8
    wb
    fnmre
    vx
    cC
    cmre
    cvv
    fnunirn
    ax-mp
    @7
    @4
    vx
    cvv
    @7
    @4
    @7
    @3
    @6
    cC
    @7
    @2
    @5
    cmre
    cC
    @5
    mreuni
    fveq2d
    eleq2d
    ibir
    rexlimivw
    sylbi
    @3
    @0
    cC
    cmre
    @2
    fvssunirn
    sseli
    impbii
end
