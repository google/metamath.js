include "col.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "clat.mm"
include "wceq.mm"
include "ollat.mm"
include "adantr.mm"
include "cops.mm"
include "olop.mm"
include "op0cl.mm"
include "syl.mm"
include "simpr.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "olj01.mm"
include "eqtrd.mm"

theorem olj02
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cX: class X
  let c.0: class .0.
  assume olj0.b: |- B = ( Base ` K )
  assume olj0.j: |- .\/ = ( join ` K )
  assume olj0.z: |- .0. = ( 0. ` K )


  assert |- ( ( K e. OL /\ X e. B ) -> ( .0. .\/ X ) = X )

  proof
    cK
    col
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    c.0
    cX
    c.or
    co
    #
    cX
    c.0
    c.or
    co
    #
    cX
    @2
    cK
    clat
    wcel
    #
    c.0
    cB
    wcel
    #
    @1
    @3
    @4
    wceq
    @0
    @5
    @1
    cK
    ollat
    adantr
    @0
    @6
    @1
    @0
    cK
    cops
    wcel
    @6
    cK
    olop
    cB
    cK
    c.0
    olj0.b
    olj0.z
    op0cl
    syl
    adantr
    @0
    @1
    simpr
    cB
    c.or
    cK
    c.0
    cX
    olj0.b
    olj0.j
    latjcom
    syl3anc
    cB
    c.or
    cK
    cX
    c.0
    olj0.b
    olj0.j
    olj0.z
    olj01
    eqtrd
end
