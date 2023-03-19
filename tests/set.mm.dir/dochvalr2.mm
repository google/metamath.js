include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "ccnv.mm"
include "crn.mm"
include "wceq.mm"
include "dihcl.mm"
include "dochvalr.mm"
include "syldan.mm"
include "dihcnvid1.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem dochvalr2
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  assume dochvalr2.b: |- B = ( Base ` K )
  assume dochvalr2.o: |- ._|_ = ( oc ` K )
  assume dochvalr2.h: |- H = ( LHyp ` K )
  assume dochvalr2.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dochvalr2.n: |- N = ( ( ocH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. B ) -> ( N ` ( I ` X ) ) = ( I ` ( ._|_ ` X ) ) )

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
    cB
    wcel
    #
    wa
    #
    cX
    cI
    cfv
    #
    cN
    cfv
    #
    @3
    cI
    ccnv
    cfv
    #
    c.pe
    cfv
    #
    cI
    cfv
    #
    cX
    c.pe
    cfv
    #
    cI
    cfv
    @0
    @1
    @3
    cI
    crn
    wcel
    @4
    @7
    wceq
    cB
    cH
    cI
    cK
    cW
    cX
    dochvalr2.b
    dochvalr2.h
    dochvalr2.i
    dihcl
    cH
    cI
    cK
    cN
    c.pe
    cW
    @3
    dochvalr2.o
    dochvalr2.h
    dochvalr2.i
    dochvalr2.n
    dochvalr
    syldan
    @2
    @6
    @8
    cI
    @2
    @5
    cX
    c.pe
    cB
    cH
    cI
    cK
    cW
    cX
    dochvalr2.b
    dochvalr2.h
    dochvalr2.i
    dihcnvid1
    fveq2d
    fveq2d
    eqtrd
end
