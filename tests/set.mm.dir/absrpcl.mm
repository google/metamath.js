include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cabs.mm"
include "cfv.mm"
include "ccj.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "crp.mm"
include "wceq.mm"
include "absval.mm"
include "adantr.mm"
include "simpl.mm"
include "cjmulrcld.mm"
include "cjmulge0d.mm"
include "cjcld.mm"
include "simpr.mm"
include "cjne0d.mm"
include "mulne0d.mm"
include "ne0gt0d.mm"
include "elrpd.mm"
include "rpsqrtcl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem absrpcl
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( abs ` A ) e. RR+ )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cA
    cabs
    cfv
    #
    cA
    cA
    ccj
    cfv
    #
    cmul
    co
    #
    csqrt
    cfv
    #
    crp
    @0
    @3
    @6
    wceq
    @1
    cA
    absval
    adantr
    @2
    @5
    crp
    wcel
    @6
    crp
    wcel
    @2
    @5
    @2
    cA
    @0
    @1
    simpl
    #
    cjmulrcld
    #
    @2
    @5
    @8
    @2
    cA
    @7
    cjmulge0d
    @2
    cA
    @4
    @7
    @2
    cA
    @7
    cjcld
    @0
    @1
    simpr
    #
    @2
    cA
    @7
    @9
    cjne0d
    mulne0d
    ne0gt0d
    elrpd
    @5
    rpsqrtcl
    syl
    eqeltrd
end
