include "cfil.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "cvv.mm"
include "wrex.mm"
include "wfn.mm"
include "wb.mm"
include "cpw.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "cfbas.mm"
include "crab.mm"
include "fvex.mm"
include "rabex.mm"
include "df-fil.mm"
include "fnmpti.mm"
include "fnunirn.mm"
include "ax-mp.mm"
include "filunibas.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "ibir.mm"
include "rexlimivw.mm"
include "sylbi.mm"
include "fvssunirn.mm"
include "sseli.mm"
include "impbii.mm"

theorem filunirn
  let cF: class F
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x


  assert |- ( F e. U. ran Fil <-> F e. ( Fil ` U. F ) )

  proof
    cF
    cfil
    crn
    cuni
    #
    wcel
    #
    cF
    cF
    cuni
    #
    cfil
    cfv
    #
    wcel
    #
    @1
    cF
    vx
    cv
    #
    cfil
    cfv
    #
    wcel
    #
    vx
    cvv
    wrex
    #
    @4
    cfil
    cvv
    wfn
    @1
    @8
    wb
    vy
    cvv
    vw
    cv
    #
    vz
    cv
    #
    cpw
    cin
    c0
    wne
    @10
    @9
    wcel
    wi
    vz
    vy
    cv
    #
    cpw
    wral
    #
    vw
    @11
    cfbas
    cfv
    #
    crab
    cfil
    @12
    vw
    @13
    @11
    cfbas
    fvex
    rabex
    vz
    vy
    vw
    df-fil
    fnmpti
    vx
    cF
    cfil
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
    cF
    @7
    @2
    @5
    cfil
    cF
    @5
    filunibas
    fveq2d
    eleq2d
    ibir
    rexlimivw
    sylbi
    @3
    @0
    cF
    cfil
    @2
    fvssunirn
    sseli
    impbii
end
