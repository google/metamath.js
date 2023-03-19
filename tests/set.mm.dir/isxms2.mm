include "cxme.mm"
include "wcel.mm"
include "ctps.mm"
include "cmopn.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cxmt.mm"
include "isxms.mm"
include "ctopon.mm"
include "istps.mm"
include "cdm.mm"
include "crn.mm"
include "cuni.mm"
include "cv.mm"
include "cbl.mm"
include "ctg.mm"
include "df-mopn.mm"
include "dmmptss.mm"
include "toponmax.mm"
include "adantl.mm"
include "simpl.mm"
include "eleqtrd.mm"
include "elfvdm.mm"
include "syl.mm"
include "sseldi.mm"
include "xmetunirn.mm"
include "sylib.mm"
include "eqid.mm"
include "mopntopon.mm"
include "eqeltrd.mm"
include "toponuni.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "ex.mm"
include "eleq1.mm"
include "syl5ibr.mm"
include "impbid.mm"
include "syl5bb.mm"
include "pm5.32ri.mm"
include "bitri.mm"

theorem isxms2
  let cD: class D
  let cJ: class J
  let cK: class K
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  assume isms.j: |- J = ( TopOpen ` K )
  assume isms.x: |- X = ( Base ` K )
  assume isms.d: |- D = ( ( dist ` K ) |` ( X X. X ) )


  assert |- ( K e. *MetSp <-> ( D e. ( *Met ` X ) /\ J = ( MetOpen ` D ) ) )

  proof
    cK
    cxme
    wcel
    cK
    ctps
    wcel
    #
    cJ
    cD
    cmopn
    cfv
    #
    wceq
    #
    wa
    cD
    cX
    cxmt
    cfv
    #
    wcel
    #
    @2
    wa
    cD
    cJ
    cK
    cX
    isms.j
    isms.x
    isms.d
    isxms
    @2
    @0
    @4
    @0
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    @2
    @4
    cX
    cJ
    cK
    isms.x
    isms.j
    istps
    @2
    @6
    @4
    @2
    @6
    @4
    @2
    @6
    wa
    #
    cD
    cD
    cdm
    cdm
    #
    cxmt
    cfv
    #
    @3
    @7
    cD
    cxmt
    crn
    cuni
    #
    wcel
    cD
    @9
    wcel
    #
    @7
    cmopn
    cdm
    #
    @10
    cD
    vx
    @10
    vx
    cv
    cbl
    cfv
    crn
    ctg
    cfv
    cmopn
    vx
    df-mopn
    dmmptss
    @7
    cX
    @1
    wcel
    cD
    @12
    wcel
    @7
    cX
    cJ
    @1
    @6
    cX
    cJ
    wcel
    @2
    cX
    cJ
    toponmax
    adantl
    @2
    @6
    simpl
    #
    eleqtrd
    cX
    cD
    cmopn
    elfvdm
    syl
    sseldi
    cD
    xmetunirn
    sylib
    #
    @7
    @8
    cX
    cxmt
    @7
    @8
    cJ
    cuni
    #
    cX
    @7
    cJ
    @8
    ctopon
    cfv
    #
    wcel
    @8
    @15
    wceq
    @7
    cJ
    @1
    @16
    @13
    @7
    @11
    @1
    @16
    wcel
    @14
    cD
    @1
    @8
    @1
    eqid
    #
    mopntopon
    syl
    eqeltrd
    @8
    cJ
    toponuni
    syl
    @6
    cX
    @15
    wceq
    @2
    cX
    cJ
    toponuni
    adantl
    eqtr4d
    fveq2d
    eleqtrd
    ex
    @4
    @6
    @2
    @1
    @5
    wcel
    cD
    @1
    cX
    @17
    mopntopon
    cJ
    @1
    @5
    eleq1
    syl5ibr
    impbid
    syl5bb
    pm5.32ri
    bitri
end
