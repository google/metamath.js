include "cops.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cple.mm"
include "wbr.mm"
include "wi.mm"
include "w3a.mm"
include "co.mm"
include "cmee.mm"
include "cp0.mm"
include "eqid.mm"
include "oposlem.mm"
include "3anidm23.mm"
include "simp2d.mm"

theorem opexmid
  let cB: class B
  let c.1: class .1.
  let c.or: class .\/
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  assume opexmid.b: |- B = ( Base ` K )
  assume opexmid.o: |- ._|_ = ( oc ` K )
  assume opexmid.j: |- .\/ = ( join ` K )
  assume opexmid.u: |- .1. = ( 1. ` K )


  assert |- ( ( K e. OP /\ X e. B ) -> ( X .\/ ( ._|_ ` X ) ) = .1. )

  proof
    cK
    cops
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    cX
    c.pe
    cfv
    #
    cB
    wcel
    @2
    c.pe
    cfv
    cX
    wceq
    cX
    cX
    cK
    cple
    cfv
    #
    wbr
    @2
    @2
    @3
    wbr
    wi
    w3a
    #
    cX
    @2
    c.or
    co
    c.1
    wceq
    #
    cX
    @2
    cK
    cmee
    cfv
    #
    co
    cK
    cp0
    cfv
    #
    wceq
    #
    @0
    @1
    @4
    @5
    @8
    w3a
    cB
    c.1
    c.or
    cK
    @3
    @6
    c.pe
    cX
    cX
    @7
    opexmid.b
    @3
    eqid
    opexmid.o
    opexmid.j
    @6
    eqid
    @7
    eqid
    opexmid.u
    oposlem
    3anidm23
    simp2d
end
