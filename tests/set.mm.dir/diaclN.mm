include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wfun.mm"
include "cdm.mm"
include "cfv.mm"
include "crn.mm"
include "wf1o.mm"
include "diaf11N.mm"
include "f1ofun.mm"
include "syl.mm"
include "fvelrn.mm"
include "sylan.mm"

theorem diaclN
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume dia1o.h: |- H = ( LHyp ` K )
  assume dia1o.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. dom I ) -> ( I ` X ) e. ran I )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cI
    wfun
    #
    cX
    cI
    cdm
    #
    wcel
    cX
    cI
    cfv
    cI
    crn
    #
    wcel
    @0
    @2
    @3
    cI
    wf1o
    @1
    cH
    cI
    cK
    cW
    dia1o.h
    dia1o.i
    diaf11N
    @2
    @3
    cI
    f1ofun
    syl
    cX
    cI
    fvelrn
    sylan
end
