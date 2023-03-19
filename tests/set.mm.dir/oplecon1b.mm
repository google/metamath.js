include "cops.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wbr.mm"
include "wb.mm"
include "opoccl.mm"
include "3adant3.mm"
include "oplecon3b.mm"
include "syld3an2.mm"
include "wceq.mm"
include "opococ.mm"
include "breq2d.mm"
include "bitrd.mm"

theorem oplecon1b
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume opcon3.b: |- B = ( Base ` K )
  assume opcon3.l: |- .<_ = ( le ` K )
  assume opcon3.o: |- ._|_ = ( oc ` K )


  assert |- ( ( K e. OP /\ X e. B /\ Y e. B ) -> ( ( ._|_ ` X ) .<_ Y <-> ( ._|_ ` Y ) .<_ X ) )

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
    c.pe
    cfv
    #
    cY
    c.le
    wbr
    #
    cY
    c.pe
    cfv
    #
    @4
    c.pe
    cfv
    #
    c.le
    wbr
    #
    @6
    cX
    c.le
    wbr
    @0
    @4
    cB
    wcel
    #
    @1
    @2
    @5
    @8
    wb
    @0
    @1
    @9
    @2
    cB
    cK
    c.pe
    cX
    opcon3.b
    opcon3.o
    opoccl
    3adant3
    cB
    cK
    c.le
    c.pe
    @4
    cY
    opcon3.b
    opcon3.l
    opcon3.o
    oplecon3b
    syld3an2
    @3
    @7
    cX
    @6
    c.le
    @0
    @1
    @7
    cX
    wceq
    @2
    cB
    cK
    c.pe
    cX
    opcon3.b
    opcon3.o
    opococ
    3adant3
    breq2d
    bitrd
end
