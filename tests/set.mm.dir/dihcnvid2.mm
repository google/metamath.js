include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "crn.mm"
include "wf1o.mm"
include "ccnv.mm"
include "wceq.mm"
include "cdvh.mm"
include "clss.mm"
include "wf1.mm"
include "eqid.mm"
include "dihf11.mm"
include "f1f1orn.mm"
include "syl.mm"
include "f1ocnvfv2.mm"
include "sylan.mm"

theorem dihcnvid2
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  assume dihcnvid2.h: |- H = ( LHyp ` K )
  assume dihcnvid2.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. ran I ) -> ( I ` ( `' I ` X ) ) = X )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cK
    cbs
    cfv
    #
    cI
    crn
    #
    cI
    wf1o
    #
    cX
    @2
    wcel
    cX
    cI
    ccnv
    cfv
    cI
    cfv
    cX
    wceq
    @0
    @1
    cW
    cK
    cdvh
    cfv
    cfv
    #
    clss
    cfv
    #
    cI
    wf1
    @3
    @1
    @5
    @4
    cH
    cI
    cK
    cW
    @1
    eqid
    dihcnvid2.h
    dihcnvid2.i
    @4
    eqid
    @5
    eqid
    dihf11
    @1
    @5
    cI
    f1f1orn
    syl
    @1
    @2
    cX
    cI
    f1ocnvfv2
    sylan
end
