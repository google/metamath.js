include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "wf1o.mm"
include "ccnv.mm"
include "cfv.mm"
include "cdvh.mm"
include "clss.mm"
include "wf1.mm"
include "eqid.mm"
include "dihf11.mm"
include "f1f1orn.mm"
include "syl.mm"
include "f1ocnvdm.mm"
include "sylan.mm"

theorem dihcnvcl
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  assume dihfn.b: |- B = ( Base ` K )
  assume dihfn.h: |- H = ( LHyp ` K )
  assume dihfn.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. ran I ) -> ( `' I ` X ) e. B )

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
    @1
    wcel
    cX
    cI
    ccnv
    cfv
    cB
    wcel
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
    dihfn.b
    dihfn.h
    dihfn.i
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
    f1ocnvdm
    sylan
end
