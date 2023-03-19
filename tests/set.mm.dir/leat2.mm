include "cops.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wo.mm"
include "leatb.mm"
include "orcom.mm"
include "neor.mm"
include "bitri.mm"
include "syl6bb.mm"
include "biimpd.mm"
include "com23.mm"
include "imp32.mm"

theorem leat2
  let cA: class A
  let cB: class B
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let c.0: class .0.
  assume leatom.b: |- B = ( Base ` K )
  assume leatom.l: |- .<_ = ( le ` K )
  assume leatom.z: |- .0. = ( 0. ` K )
  assume leatom.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. OP /\ X e. B /\ P e. A ) /\ ( X =/= .0. /\ X .<_ P ) ) -> X = P )

  proof
    cK
    cops
    wcel
    cX
    cB
    wcel
    cP
    cA
    wcel
    w3a
    #
    cX
    c.0
    wne
    #
    cX
    cP
    c.le
    wbr
    #
    cX
    cP
    wceq
    #
    @0
    @2
    @1
    @3
    @0
    @2
    @1
    @3
    wi
    #
    @0
    @2
    @3
    cX
    c.0
    wceq
    #
    wo
    #
    @4
    cA
    cB
    cP
    cK
    c.le
    cX
    c.0
    leatom.b
    leatom.l
    leatom.z
    leatom.a
    leatb
    @6
    @5
    @3
    wo
    @4
    @3
    @5
    orcom
    @3
    cX
    c.0
    neor
    bitri
    syl6bb
    biimpd
    com23
    imp32
end
