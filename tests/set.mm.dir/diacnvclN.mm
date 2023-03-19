include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "crn.mm"
include "wf1o.mm"
include "ccnv.mm"
include "cfv.mm"
include "diaf11N.mm"
include "f1ocnvdm.mm"
include "sylan.mm"

theorem diacnvclN
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume dia1o.h: |- H = ( LHyp ` K )
  assume dia1o.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. ran I ) -> ( `' I ` X ) e. dom I )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cI
    cdm
    #
    cI
    crn
    #
    cI
    wf1o
    cX
    @1
    wcel
    cX
    cI
    ccnv
    cfv
    @0
    wcel
    cH
    cI
    cK
    cW
    dia1o.h
    dia1o.i
    diaf11N
    @0
    @1
    cX
    cI
    f1ocnvdm
    sylan
end
