include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cin.mm"
include "cun.mm"
include "wceq.mm"
include "djhval.mm"
include "3impb.mm"
include "dochdmj1.mm"
include "fveq2d.mm"
include "eqtr4d.mm"

theorem djhval2
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  assume djhval.h: |- H = ( LHyp ` K )
  assume djhval.u: |- U = ( ( DVecH ` K ) ` W )
  assume djhval.v: |- V = ( Base ` U )
  assume djhval.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume djhval.j: |- .\/ = ( ( joinH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X C_ V /\ Y C_ V ) -> ( X .\/ Y ) = ( ._|_ ` ( ._|_ ` ( X u. Y ) ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cV
    wss
    #
    cY
    cV
    wss
    #
    w3a
    #
    cX
    cY
    c.or
    co
    #
    cX
    c.pe
    cfv
    cY
    c.pe
    cfv
    cin
    #
    c.pe
    cfv
    #
    cX
    cY
    cun
    c.pe
    cfv
    #
    c.pe
    cfv
    @0
    @1
    @2
    @4
    @6
    wceq
    cU
    cH
    c.or
    cK
    c.pe
    cV
    cW
    cX
    cY
    djhval.h
    djhval.u
    djhval.v
    djhval.o
    djhval.j
    djhval
    3impb
    @3
    @7
    @5
    c.pe
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    cY
    djhval.h
    djhval.u
    djhval.v
    djhval.o
    dochdmj1
    fveq2d
    eqtr4d
end
