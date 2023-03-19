include "cops.mm"
include "wcel.mm"
include "w3a.mm"
include "wceq.mm"
include "cfv.mm"
include "fveq2.mm"
include "eqcoms.mm"
include "opococ.mm"
include "3adant3.mm"
include "3adant2.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "impbid2.mm"

theorem opcon3b
  let cB: class B
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume opoccl.b: |- B = ( Base ` K )
  assume opoccl.o: |- ._|_ = ( oc ` K )


  assert |- ( ( K e. OP /\ X e. B /\ Y e. B ) -> ( X = Y <-> ( ._|_ ` Y ) = ( ._|_ ` X ) ) )

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
    wceq
    #
    cY
    c.pe
    cfv
    #
    cX
    c.pe
    cfv
    #
    wceq
    #
    @7
    cY
    cX
    cY
    cX
    c.pe
    fveq2
    eqcoms
    @7
    @6
    c.pe
    cfv
    #
    @5
    c.pe
    cfv
    #
    wceq
    #
    @3
    @4
    @10
    @6
    @5
    @6
    @5
    c.pe
    fveq2
    eqcoms
    @3
    @8
    cX
    @9
    cY
    @0
    @1
    @8
    cX
    wceq
    @2
    cB
    cK
    c.pe
    cX
    opoccl.b
    opoccl.o
    opococ
    3adant3
    @0
    @2
    @9
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
    eqeq12d
    syl5ib
    impbid2
end
