include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "cv.mm"
include "ccnv.mm"
include "cfv.mm"
include "dihcnvid2.mm"
include "cbs.mm"
include "eqid.mm"
include "dihcnvcl.mm"
include "dihlss.mm"
include "syldan.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "ssrdv.mm"

theorem dihsslss
  let cS: class S
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let vx: setvar x
  assume dihsslss.h: |- H = ( LHyp ` K )
  assume dihsslss.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihsslss.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihsslss.s: |- S = ( LSubSp ` U )


  assert |- ( ( K e. HL /\ W e. H ) -> ran I C_ S )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    vx
    cI
    crn
    #
    cS
    @0
    vx
    cv
    #
    @1
    wcel
    #
    @2
    cS
    wcel
    @0
    @3
    wa
    @2
    cI
    ccnv
    cfv
    #
    cI
    cfv
    #
    @2
    cS
    cH
    cI
    cK
    cW
    @2
    dihsslss.h
    dihsslss.i
    dihcnvid2
    @0
    @3
    @4
    cK
    cbs
    cfv
    #
    wcel
    @5
    cS
    wcel
    @6
    cH
    cI
    cK
    cW
    @2
    @6
    eqid
    #
    dihsslss.h
    dihsslss.i
    dihcnvcl
    @6
    cS
    cU
    cH
    cI
    cK
    cW
    @4
    @7
    dihsslss.h
    dihsslss.i
    dihsslss.u
    dihsslss.s
    dihlss
    syldan
    eqeltrrd
    ex
    ssrdv
end
