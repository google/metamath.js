include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "wf1o.mm"
include "cfv.mm"
include "ccnv.mm"
include "wceq.mm"
include "cdvh.mm"
include "clss.mm"
include "wf1.mm"
include "eqid.mm"
include "dihf11.mm"
include "f1f1orn.mm"
include "syl.mm"
include "f1ocnvfv1.mm"
include "sylan.mm"

theorem dihcnvid1
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  assume dihcnvid1.b: |- B = ( Base ` K )
  assume dihcnvid1.h: |- H = ( LHyp ` K )
  assume dihcnvid1.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. B ) -> ( `' I ` ( I ` X ) ) = X )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cB
    cI
    crn
    #
    cI
    wf1o
    #
    cX
    cB
    wcel
    cX
    cI
    cfv
    cI
    ccnv
    cfv
    cX
    wceq
    @0
    cB
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
    @2
    cB
    @4
    @3
    cH
    cI
    cK
    cW
    dihcnvid1.b
    dihcnvid1.h
    dihcnvid1.i
    @3
    eqid
    @4
    eqid
    dihf11
    cB
    @4
    cI
    f1f1orn
    syl
    cB
    @1
    cX
    cI
    f1ocnvfv1
    sylan
end
