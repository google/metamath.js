include "catm.mm"
include "cfv.mm"
include "coc.mm"
include "cdvh.mm"
include "clsm.mm"
include "cltrn.mm"
include "ctendo.mm"
include "cv.mm"
include "wceq.mm"
include "crio.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "eqid.mm"
include "dihord6apre.mm"

theorem dihord6a
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  let vq: setvar q
  let vr: setvar r
  let vh: setvar h
  assume dihord3.b: |- B = ( Base ` K )
  assume dihord3.l: |- .<_ = ( le ` K )
  assume dihord3.h: |- H = ( LHyp ` K )
  assume dihord3.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ ( Y e. B /\ Y .<_ W ) ) /\ ( I ` X ) C_ ( I ` Y ) ) -> X .<_ Y )

  proof
    cK
    catm
    cfv
    #
    cB
    cW
    cK
    coc
    cfv
    cfv
    #
    cW
    cK
    cdvh
    cfv
    cfv
    #
    clsm
    cfv
    #
    cW
    cK
    cltrn
    cfv
    cfv
    #
    @2
    vh
    cW
    cK
    ctendo
    cfv
    cfv
    #
    @1
    vh
    cv
    cfv
    vq
    cv
    wceq
    vh
    @4
    crio
    #
    cH
    cI
    cK
    c.le
    vh
    @4
    cid
    cB
    cres
    cmpt
    #
    cW
    cX
    cY
    vq
    dihord3.b
    dihord3.l
    @0
    eqid
    dihord3.h
    @1
    eqid
    @7
    eqid
    @4
    eqid
    @5
    eqid
    dihord3.i
    @2
    eqid
    @3
    eqid
    @6
    eqid
    dihord6apre
end
