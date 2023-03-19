include "cops.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cple.mm"
include "wbr.mm"
include "wi.mm"
include "w3a.mm"
include "cjn.mm"
include "co.mm"
include "cp1.mm"
include "cmee.mm"
include "cp0.mm"
include "eqid.mm"
include "oposlem.mm"
include "3anidm23.mm"
include "simp1d.mm"

theorem opoccl
  let cB: class B
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  assume opoccl.b: |- B = ( Base ` K )
  assume opoccl.o: |- ._|_ = ( oc ` K )


  assert |- ( ( K e. OP /\ X e. B ) -> ( ._|_ ` X ) e. B )

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
    #
    cX
    c.pe
    cfv
    #
    cB
    wcel
    #
    @3
    c.pe
    cfv
    cX
    wceq
    #
    cX
    cX
    cK
    cple
    cfv
    #
    wbr
    @3
    @3
    @6
    wbr
    wi
    #
    @2
    @4
    @5
    @7
    w3a
    #
    cX
    @3
    cK
    cjn
    cfv
    #
    co
    cK
    cp1
    cfv
    #
    wceq
    #
    cX
    @3
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
    @8
    @11
    @14
    w3a
    cB
    @10
    @9
    cK
    @6
    @12
    c.pe
    cX
    cX
    @13
    opoccl.b
    @6
    eqid
    opoccl.o
    @9
    eqid
    @12
    eqid
    @13
    eqid
    @10
    eqid
    oposlem
    3anidm23
    simp1d
    simp1d
end
