include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "ccnv.mm"
include "cfv.mm"
include "cdm.mm"
include "wceq.mm"
include "diacnvclN.mm"
include "doca2N.mm"
include "syldan.mm"
include "wf1o.mm"
include "diaf11N.mm"
include "f1ocnvfv2.mm"
include "sylan.mm"
include "fveq2d.mm"
include "3eqtr3d.mm"

theorem doca3N
  let cH: class H
  let cI: class I
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  assume doca2.h: |- H = ( LHyp ` K )
  assume doca2.i: |- I = ( ( DIsoA ` K ) ` W )
  assume doca2.n: |- ._|_ = ( ( ocA ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. ran I ) -> ( ._|_ ` ( ._|_ ` X ) ) = X )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cI
    crn
    #
    wcel
    #
    wa
    #
    cX
    cI
    ccnv
    cfv
    #
    cI
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @5
    cX
    c.pe
    cfv
    #
    c.pe
    cfv
    cX
    @0
    @2
    @4
    cI
    cdm
    #
    wcel
    @7
    @5
    wceq
    cH
    cI
    cK
    cW
    cX
    doca2.h
    doca2.i
    diacnvclN
    cH
    cI
    cK
    c.pe
    cW
    @4
    doca2.h
    doca2.i
    doca2.n
    doca2N
    syldan
    @3
    @6
    @8
    c.pe
    @3
    @5
    cX
    c.pe
    @0
    @9
    @1
    cI
    wf1o
    @2
    @5
    cX
    wceq
    cH
    cI
    cK
    cW
    doca2.h
    doca2.i
    diaf11N
    @9
    @1
    cX
    cI
    f1ocnvfv2
    sylan
    #
    fveq2d
    fveq2d
    @10
    3eqtr3d
end
