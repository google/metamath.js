include "catm.mm"
include "cfv.mm"
include "cdvh.mm"
include "clsm.mm"
include "cjn.mm"
include "cmee.mm"
include "eqid.mm"
include "dihord5apre.mm"

theorem dihord5a
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dihord.b: |- B = ( Base ` K )
  assume dihord.l: |- .<_ = ( le ` K )
  assume dihord.h: |- H = ( LHyp ` K )
  assume dihord.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ X .<_ W ) /\ ( Y e. B /\ -. Y .<_ W ) ) /\ ( I ` X ) C_ ( I ` Y ) ) -> X .<_ Y )

  proof
    cK
    catm
    cfv
    #
    cB
    cW
    cK
    cdvh
    cfv
    cfv
    #
    clsm
    cfv
    #
    @1
    cH
    cI
    cK
    cjn
    cfv
    #
    cK
    c.le
    cK
    cmee
    cfv
    #
    cW
    cX
    cY
    dihord.b
    dihord.l
    dihord.h
    @3
    eqid
    @4
    eqid
    @0
    eqid
    @1
    eqid
    @2
    eqid
    dihord.i
    dihord5apre
end
