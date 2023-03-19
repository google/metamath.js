include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "wfn.mm"
include "cdm.mm"
include "wceq.mm"
include "dibfnN.mm"
include "fndm.mm"
include "syl.mm"

theorem dibdmN
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
  assert |- ( ( K e. V /\ W e. H ) -> dom I = { x e. B | x .<_ W } )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
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
    cI
    cdm
    @0
    wceq
    vx
    cB
    cH
    cI
    cK
    c.le
    cV
    cW
    dibfn.b
    dibfn.l
    dibfn.h
    dibfn.i
    dibfnN
    @0
    cI
    fndm
    syl
end
