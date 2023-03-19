include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "wf1.mm"
include "crn.mm"
include "wf1o.mm"
include "diaf11N.mm"
include "f1of1.mm"
include "syl.mm"
include "wb.mm"
include "diarnN.mm"
include "f1eq3.mm"
include "mpbid.mm"
include "dff1o5.mm"
include "sylanbrc.mm"

theorem diaf1oN
  let vx: setvar x
  let cS: class S
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  assume dvadia.h: |- H = ( LHyp ` K )
  assume dvadia.u: |- U = ( ( DVecA ` K ) ` W )
  assume dvadia.i: |- I = ( ( DIsoA ` K ) ` W )
  assume dvadia.n: |- ._|_ = ( ( ocA ` K ) ` W )
  assume dvadia.s: |- S = ( LSubSp ` U )

  disjoint H x
  disjoint I x
  disjoint K x
  disjoint S x
  disjoint W x
  assert |- ( ( K e. HL /\ W e. H ) -> I : dom I -1-1-onto-> { x e. S | ( ._|_ ` ( ._|_ ` x ) ) = x } )

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
    cdm
    #
    vx
    cv
    #
    c.pe
    cfv
    c.pe
    cfv
    @2
    wceq
    vx
    cS
    crab
    #
    cI
    wf1
    #
    cI
    crn
    #
    @3
    wceq
    #
    @1
    @3
    cI
    wf1o
    @0
    @1
    @5
    cI
    wf1
    #
    @4
    @0
    @1
    @5
    cI
    wf1o
    @7
    cH
    cI
    cK
    cW
    dvadia.h
    dvadia.i
    diaf11N
    @1
    @5
    cI
    f1of1
    syl
    @0
    @6
    @7
    @4
    wb
    vx
    cS
    cU
    cH
    cI
    cK
    c.pe
    cW
    dvadia.h
    dvadia.u
    dvadia.i
    dvadia.n
    dvadia.s
    diarnN
    #
    @5
    @3
    @1
    cI
    f1eq3
    syl
    mpbid
    @8
    @1
    @3
    cI
    dff1o5
    sylanbrc
end
