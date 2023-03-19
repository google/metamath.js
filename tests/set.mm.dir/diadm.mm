include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "wfn.mm"
include "cdm.mm"
include "wceq.mm"
include "diafn.mm"
include "fndm.mm"
include "syl.mm"

theorem diadm
  let vx: setvar x
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let vy: setvar y
  let vf: setvar f
  let cX: class X
  assume diafn.b: |- B = ( Base ` K )
  assume diafn.l: |- .<_ = ( le ` K )
  assume diafn.h: |- H = ( LHyp ` K )
  assume diafn.i: |- I = ( ( DIsoA ` K ) ` W )

  disjoint .<_ x
  disjoint B x
  disjoint K x
  disjoint W x
  disjoint x y
  disjoint .<_ y
  disjoint B y
  disjoint f x
  disjoint f y
  disjoint K f
  disjoint K y
  disjoint W f
  disjoint W y
  disjoint X x
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
    diafn.b
    diafn.l
    diafn.h
    diafn.i
    diafn
    @0
    cI
    fndm
    syl
end
