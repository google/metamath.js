include "cops.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wceq.mm"
include "op0le.mm"
include "biantrud.mm"
include "cpo.mm"
include "wb.mm"
include "opposet.mm"
include "adantr.mm"
include "simpr.mm"
include "op0cl.mm"
include "posasymb.mm"
include "syl3anc.mm"
include "bitrd.mm"

theorem ople0
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let c.0: class .0.
  assume op0le.b: |- B = ( Base ` K )
  assume op0le.l: |- .<_ = ( le ` K )
  assume op0le.z: |- .0. = ( 0. ` K )


  assert |- ( ( K e. OP /\ X e. B ) -> ( X .<_ .0. <-> X = .0. ) )

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
    c.0
    c.le
    wbr
    #
    @3
    c.0
    cX
    c.le
    wbr
    #
    wa
    #
    cX
    c.0
    wceq
    #
    @2
    @4
    @3
    cB
    cK
    c.le
    cX
    c.0
    op0le.b
    op0le.l
    op0le.z
    op0le
    biantrud
    @2
    cK
    cpo
    wcel
    #
    @1
    c.0
    cB
    wcel
    #
    @5
    @6
    wb
    @0
    @7
    @1
    cK
    opposet
    adantr
    @0
    @1
    simpr
    @0
    @8
    @1
    cB
    cK
    c.0
    op0le.b
    op0le.z
    op0cl
    adantr
    cB
    cK
    c.le
    cX
    c.0
    op0le.b
    op0le.l
    posasymb
    syl3anc
    bitrd
end
