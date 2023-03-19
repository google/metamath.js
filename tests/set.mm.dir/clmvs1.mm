include "cclm.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "co.mm"
include "csca.mm"
include "cfv.mm"
include "cur.mm"
include "wceq.mm"
include "eqid.mm"
include "clm1.mm"
include "adantr.mm"
include "oveq1d.mm"
include "clmod.mm"
include "clmlmod.mm"
include "lmodvs1.mm"
include "sylan.mm"
include "eqtrd.mm"

theorem clmvs1
  let c.x: class .x.
  let cV: class V
  let cW: class W
  let cX: class X
  assume clmvs1.v: |- V = ( Base ` W )
  assume clmvs1.s: |- .x. = ( .s ` W )


  assert |- ( ( W e. CMod /\ X e. V ) -> ( 1 .x. X ) = X )

  proof
    cW
    cclm
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    #
    c1
    cX
    c.x
    co
    cW
    csca
    cfv
    #
    cur
    cfv
    #
    cX
    c.x
    co
    #
    cX
    @2
    c1
    @4
    cX
    c.x
    @0
    c1
    @4
    wceq
    @1
    @3
    cW
    @3
    eqid
    #
    clm1
    adantr
    oveq1d
    @0
    cW
    clmod
    wcel
    @1
    @5
    cX
    wceq
    cW
    clmlmod
    c.x
    @4
    @3
    cV
    cW
    cX
    clmvs1.v
    @6
    clmvs1.s
    @4
    eqid
    lmodvs1
    sylan
    eqtrd
end
