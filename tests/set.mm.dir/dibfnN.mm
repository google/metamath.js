include "wcel.mm"
include "wa.mm"
include "cdia.mm"
include "cfv.mm"
include "cdm.mm"
include "wfn.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "eqid.mm"
include "dibfna.mm"
include "diadm.mm"
include "fneq2d.mm"
include "mpbid.mm"

theorem dibfnN
  let vx: setvar x
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  assume dibfn.b: |- B = ( Base ` K )
  assume dibfn.l: |- .<_ = ( le ` K )
  assume dibfn.h: |- H = ( LHyp ` K )
  assume dibfn.i: |- I = ( ( DIsoB ` K ) ` W )

  disjoint .<_ x
  disjoint B x
  disjoint K x
  disjoint W x
  assert |- ( ( K e. V /\ W e. H ) -> I Fn { x e. B | x .<_ W } )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cI
    cW
    cK
    cdia
    cfv
    cfv
    #
    cdm
    #
    wfn
    cI
    vx
    cv
    cW
    c.le
    wbr
    vx
    cB
    crab
    #
    wfn
    cH
    cI
    @1
    cK
    cV
    cW
    dibfn.h
    @1
    eqid
    #
    dibfn.i
    dibfna
    @0
    @2
    @3
    cI
    vx
    cB
    cH
    @1
    cK
    c.le
    cV
    cW
    dibfn.b
    dibfn.l
    dibfn.h
    @4
    diadm
    fneq2d
    mpbid
end
