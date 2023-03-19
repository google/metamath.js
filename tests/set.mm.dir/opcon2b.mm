include "cops.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "wb.mm"
include "opoccl.mm"
include "3adant2.mm"
include "opcon3b.mm"
include "syld3an3.mm"
include "opococ.mm"
include "eqeq1d.mm"
include "bitrd.mm"

theorem opcon2b
  let cB: class B
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume opoccl.b: |- B = ( Base ` K )
  assume opoccl.o: |- ._|_ = ( oc ` K )


  assert |- ( ( K e. OP /\ X e. B /\ Y e. B ) -> ( X = ( ._|_ ` Y ) <-> Y = ( ._|_ ` X ) ) )

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
    wceq
    #
    @4
    c.pe
    cfv
    #
    cX
    c.pe
    cfv
    #
    wceq
    #
    cY
    @7
    wceq
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
    opoccl.b
    opoccl.o
    opoccl
    3adant2
    cB
    cK
    c.pe
    cX
    @4
    opoccl.b
    opoccl.o
    opcon3b
    syld3an3
    @3
    @6
    cY
    @7
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
    opoccl.b
    opoccl.o
    opococ
    3adant2
    eqeq1d
    bitrd
end
