include "cops.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "wceq.mm"
include "op0le.mm"
include "3adant2.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "necon3bd.mm"
include "imp.mm"

theorem opnlen0
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume op0le.b: |- B = ( Base ` K )
  assume op0le.l: |- .<_ = ( le ` K )
  assume op0le.z: |- .0. = ( 0. ` K )


  assert |- ( ( ( K e. OP /\ X e. B /\ Y e. B ) /\ -. X .<_ Y ) -> X =/= .0. )

  proof
    cK
    cops
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.le
    wbr
    #
    wn
    cX
    c.0
    wne
    @3
    @4
    cX
    c.0
    @3
    @4
    cX
    c.0
    wceq
    c.0
    cY
    c.le
    wbr
    #
    @0
    @2
    @5
    @1
    cB
    cK
    c.le
    cY
    c.0
    op0le.b
    op0le.l
    op0le.z
    op0le
    3adant2
    cX
    c.0
    cY
    c.le
    breq1
    syl5ibrcom
    necon3bd
    imp
end
