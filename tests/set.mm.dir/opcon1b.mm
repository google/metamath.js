include "cops.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "opcon2b.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "bicomd.mm"

theorem opcon1b
  let cB: class B
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume opoccl.b: |- B = ( Base ` K )
  assume opoccl.o: |- ._|_ = ( oc ` K )


  assert |- ( ( K e. OP /\ X e. B /\ Y e. B ) -> ( ( ._|_ ` X ) = Y <-> ( ._|_ ` Y ) = X ) )

  proof
    cK
    cops
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    w3a
    #
    cY
    c.pe
    cfv
    #
    cX
    wceq
    #
    cX
    c.pe
    cfv
    #
    cY
    wceq
    #
    @0
    cX
    @1
    wceq
    cY
    @3
    wceq
    @2
    @4
    cB
    cK
    c.pe
    cX
    cY
    opoccl.b
    opoccl.o
    opcon2b
    @1
    cX
    eqcom
    @3
    cY
    eqcom
    3bitr4g
    bicomd
end
