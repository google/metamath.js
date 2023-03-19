include "cxmt.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "cv.mm"
include "cvv.mm"
include "wrex.mm"
include "wfn.mm"
include "wb.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "cxr.mm"
include "cxp.mm"
include "cmap.mm"
include "crab.mm"
include "ovex.mm"
include "rabex.mm"
include "df-xmet.mm"
include "fnmpti.mm"
include "fnunirn.mm"
include "ax-mp.mm"
include "id.mm"
include "xmetdmdm.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "rexlimivw.mm"
include "sylbi.mm"
include "fvssunirn.mm"
include "sseli.mm"
include "impbii.mm"

theorem xmetunirn
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vd: setvar d
  let vw: setvar w
  let cR: class R
  let cX: class X
  let cC: class C


  assert |- ( D e. U. ran *Met <-> D e. ( *Met ` dom dom D ) )

  proof
    cD
    cxmt
    crn
    cuni
    #
    wcel
    #
    cD
    cD
    cdm
    cdm
    #
    cxmt
    cfv
    #
    wcel
    #
    @1
    cD
    vx
    cv
    #
    cxmt
    cfv
    #
    wcel
    #
    vx
    cvv
    wrex
    #
    @4
    cxmt
    cvv
    wfn
    @1
    @8
    wb
    vx
    cvv
    vy
    cv
    #
    vz
    cv
    #
    vd
    cv
    #
    co
    #
    cc0
    wceq
    @9
    @10
    wceq
    wb
    @12
    vw
    cv
    #
    @9
    @11
    co
    @13
    @10
    @11
    co
    cxad
    co
    cle
    wbr
    vw
    @5
    wral
    wa
    vz
    @5
    wral
    vy
    @5
    wral
    #
    vd
    cxr
    @5
    @5
    cxp
    #
    cmap
    co
    #
    crab
    cxmt
    @14
    vd
    @16
    cxr
    @15
    cmap
    ovex
    rabex
    vx
    vy
    vz
    vw
    vd
    df-xmet
    fnmpti
    vx
    cD
    cxmt
    cvv
    fnunirn
    ax-mp
    @7
    @4
    vx
    cvv
    @7
    cD
    @6
    @3
    @7
    id
    @7
    @5
    @2
    cxmt
    cD
    @5
    xmetdmdm
    fveq2d
    eleqtrd
    rexlimivw
    sylbi
    @3
    @0
    cD
    cxmt
    @2
    fvssunirn
    sseli
    impbii
end
