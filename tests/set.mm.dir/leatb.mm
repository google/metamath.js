include "cops.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "op0le.mm"
include "3adant3.mm"
include "biantrurd.mm"
include "cpo.mm"
include "ccvr.mm"
include "cfv.mm"
include "wb.mm"
include "opposet.mm"
include "3ad2ant1.mm"
include "op0cl.mm"
include "atbase.mm"
include "id.mm"
include "3anim123i.mm"
include "3com23.mm"
include "eqid.mm"
include "atcvr0.mm"
include "3adant2.mm"
include "cvrnbtwn4.mm"
include "syl3anc.mm"
include "eqcom.mm"
include "orbi1i.mm"
include "syl6bb.mm"
include "bitrd.mm"
include "orcom.mm"

theorem leatb
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


  assert |- ( ( K e. OP /\ X e. B /\ P e. A ) -> ( X .<_ P <-> ( X = P \/ X = .0. ) ) )

  proof
    cK
    cops
    wcel
    #
    cX
    cB
    wcel
    #
    cP
    cA
    wcel
    #
    w3a
    #
    cX
    cP
    c.le
    wbr
    #
    cX
    c.0
    wceq
    #
    cX
    cP
    wceq
    #
    wo
    #
    @6
    @5
    wo
    @3
    @4
    c.0
    cX
    c.le
    wbr
    #
    @4
    wa
    #
    @7
    @3
    @8
    @4
    @0
    @1
    @8
    @2
    cB
    cK
    c.le
    cX
    c.0
    leatom.b
    leatom.l
    leatom.z
    op0le
    3adant3
    biantrurd
    @3
    @9
    c.0
    cX
    wceq
    #
    @6
    wo
    #
    @7
    @3
    cK
    cpo
    wcel
    #
    c.0
    cB
    wcel
    #
    cP
    cB
    wcel
    #
    @1
    w3a
    #
    c.0
    cP
    cK
    ccvr
    cfv
    #
    wbr
    #
    @9
    @11
    wb
    @0
    @1
    @12
    @2
    cK
    opposet
    3ad2ant1
    @0
    @2
    @1
    @15
    @0
    @13
    @2
    @14
    @1
    @1
    cB
    cK
    c.0
    leatom.b
    leatom.z
    op0cl
    cA
    cB
    cP
    cK
    leatom.b
    leatom.a
    atbase
    @1
    id
    3anim123i
    3com23
    @0
    @2
    @17
    @1
    cA
    @16
    cops
    cP
    cK
    c.0
    leatom.z
    @16
    eqid
    #
    leatom.a
    atcvr0
    3adant2
    cB
    @16
    cK
    c.le
    c.0
    cP
    cX
    leatom.b
    leatom.l
    @18
    cvrnbtwn4
    syl3anc
    @10
    @5
    @6
    c.0
    cX
    eqcom
    orbi1i
    syl6bb
    bitrd
    @5
    @6
    orcom
    syl6bb
end
