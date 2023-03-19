include "cclm.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "neg1mulneg1e1.mm"
include "oveq1i.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "wceq.mm"
include "simpl.mm"
include "eqid.mm"
include "clmneg1.mm"
include "adantr.mm"
include "simpr.mm"
include "clmvsass.mm"
include "syl13anc.mm"
include "clmvs1.mm"
include "3eqtr3a.mm"

theorem clmnegneg
  let cA: class A
  let c.pl: class .+
  let c.x: class .x.
  let cV: class V
  let cW: class W
  assume clmpm1dir.v: |- V = ( Base ` W )
  assume clmpm1dir.s: |- .x. = ( .s ` W )
  assume clmpm1dir.a: |- .+ = ( +g ` W )


  assert |- ( ( W e. CMod /\ A e. V ) -> ( -u 1 .x. ( -u 1 .x. A ) ) = A )

  proof
    cW
    cclm
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    c1
    cneg
    #
    @3
    cmul
    co
    #
    cA
    c.x
    co
    #
    c1
    cA
    c.x
    co
    @3
    @3
    cA
    c.x
    co
    c.x
    co
    #
    cA
    @4
    c1
    cA
    c.x
    neg1mulneg1e1
    oveq1i
    @2
    @0
    @3
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @9
    @1
    @5
    @6
    wceq
    @0
    @1
    simpl
    @0
    @9
    @1
    @7
    @8
    cW
    @7
    eqid
    #
    @8
    eqid
    #
    clmneg1
    adantr
    #
    @12
    @0
    @1
    simpr
    @3
    @3
    c.x
    @7
    @8
    cV
    cW
    cA
    clmpm1dir.v
    @10
    clmpm1dir.s
    @11
    clmvsass
    syl13anc
    c.x
    cV
    cW
    cA
    clmpm1dir.v
    clmpm1dir.s
    clmvs1
    3eqtr3a
end
