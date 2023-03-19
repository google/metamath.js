include "cops.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wbr.mm"
include "wb.mm"
include "opoccl.mm"
include "3adant3.mm"
include "opltcon3b.mm"
include "syld3an2.mm"
include "wceq.mm"
include "opococ.mm"
include "breq2d.mm"
include "bitrd.mm"

theorem opltcon1b
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume opltcon3.b: |- B = ( Base ` K )
  assume opltcon3.s: |- .< = ( lt ` K )
  assume opltcon3.o: |- ._|_ = ( oc ` K )


  assert |- ( ( K e. OP /\ X e. B /\ Y e. B ) -> ( ( ._|_ ` X ) .< Y <-> ( ._|_ ` Y ) .< X ) )

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
    c.lt
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
    c.lt
    wbr
    #
    @6
    cX
    c.lt
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
    opltcon3.b
    opltcon3.o
    opoccl
    3adant3
    cB
    c.lt
    cK
    c.pe
    @4
    cY
    opltcon3.b
    opltcon3.s
    opltcon3.o
    opltcon3b
    syld3an2
    @3
    @7
    cX
    @6
    c.lt
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
    opltcon3.b
    opltcon3.o
    opococ
    3adant3
    breq2d
    bitrd
end
