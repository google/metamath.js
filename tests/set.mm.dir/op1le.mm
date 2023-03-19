include "cops.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wceq.mm"
include "ople1.mm"
include "biantrurd.mm"
include "cpo.mm"
include "wb.mm"
include "opposet.mm"
include "adantr.mm"
include "simpr.mm"
include "op1cl.mm"
include "posasymb.mm"
include "syl3anc.mm"
include "bitrd.mm"

theorem op1le
  let cB: class B
  let c.1: class .1.
  let cK: class K
  let c.le: class .<_
  let cX: class X
  assume ople1.b: |- B = ( Base ` K )
  assume ople1.l: |- .<_ = ( le ` K )
  assume ople1.u: |- .1. = ( 1. ` K )


  assert |- ( ( K e. OP /\ X e. B ) -> ( .1. .<_ X <-> X = .1. ) )

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
    c.1
    cX
    c.le
    wbr
    #
    cX
    c.1
    c.le
    wbr
    #
    @3
    wa
    #
    cX
    c.1
    wceq
    #
    @2
    @4
    @3
    cB
    c.1
    cK
    c.le
    cX
    ople1.b
    ople1.l
    ople1.u
    ople1
    biantrurd
    @2
    cK
    cpo
    wcel
    #
    @1
    c.1
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
    c.1
    cK
    ople1.b
    ople1.u
    op1cl
    adantr
    cB
    cK
    c.le
    cX
    c.1
    ople1.b
    ople1.l
    posasymb
    syl3anc
    bitrd
end
