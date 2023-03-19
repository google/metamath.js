include "cusp.mm"
include "wcel.mm"
include "cha.mm"
include "wa.mm"
include "cuss.mm"
include "cfv.mm"
include "cutop.mm"
include "creg.mm"
include "wceq.mm"
include "cbs.mm"
include "cust.mm"
include "eqid.mm"
include "isusp.mm"
include "simprbi.mm"
include "adantr.mm"
include "simplbi.mm"
include "simpr.mm"
include "eqeltrrd.mm"
include "utopreg.mm"
include "syl2anc.mm"
include "eqeltrd.mm"

theorem uspreg
  let cJ: class J
  let cW: class W
  assume uspreg.1: |- J = ( TopOpen ` W )


  assert |- ( ( W e. UnifSp /\ J e. Haus ) -> J e. Reg )

  proof
    cW
    cusp
    wcel
    #
    cJ
    cha
    wcel
    #
    wa
    #
    cJ
    cW
    cuss
    cfv
    #
    cutop
    cfv
    #
    creg
    @0
    cJ
    @4
    wceq
    #
    @1
    @0
    @3
    cW
    cbs
    cfv
    #
    cust
    cfv
    wcel
    #
    @5
    @6
    @3
    cJ
    cW
    @6
    eqid
    @3
    eqid
    uspreg.1
    isusp
    #
    simprbi
    adantr
    #
    @2
    @7
    @4
    cha
    wcel
    @4
    creg
    wcel
    @0
    @7
    @1
    @0
    @7
    @5
    @8
    simplbi
    adantr
    @2
    cJ
    @4
    cha
    @9
    @0
    @1
    simpr
    eqeltrrd
    @3
    @4
    @6
    @4
    eqid
    utopreg
    syl2anc
    eqeltrd
end
