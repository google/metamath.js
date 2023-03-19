include "cops.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wbr.mm"
include "wb.mm"
include "opoccl.mm"
include "3adant2.mm"
include "opltcon3b.mm"
include "syld3an3.mm"
include "wceq.mm"
include "opococ.mm"
include "breq1d.mm"
include "bitrd.mm"

theorem opltcon2b
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume opltcon3.b: |- B = ( Base ` K )
  assume opltcon3.s: |- .< = ( lt ` K )
  assume opltcon3.o: |- ._|_ = ( oc ` K )


  assert |- ( ( K e. OP /\ X e. B /\ Y e. B ) -> ( X .< ( ._|_ ` Y ) <-> Y .< ( ._|_ ` X ) ) )

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
    c.pe
    cfv
    #
    c.lt
    wbr
    #
    @4
    c.pe
    cfv
    #
    cX
    c.pe
    cfv
    #
    c.lt
    wbr
    #
    cY
    @7
    c.lt
    wbr
    @0
    @1
    @2
    @4
    cB
    wcel
    #
    @5
    @8
    wb
    @0
    @2
    @9
    @1
    cB
    cK
    c.pe
    cY
    opltcon3.b
    opltcon3.o
    opoccl
    3adant2
    cB
    c.lt
    cK
    c.pe
    cX
    @4
    opltcon3.b
    opltcon3.s
    opltcon3.o
    opltcon3b
    syld3an3
    @3
    @6
    cY
    @7
    c.lt
    @0
    @2
    @6
    cY
    wceq
    @1
    cB
    cK
    c.pe
    cY
    opltcon3.b
    opltcon3.o
    opococ
    3adant2
    breq1d
    bitrd
end
