include "cxr.mm"
include "wcel.mm"
include "cmnf.mm"
include "wne.mm"
include "wa.mm"
include "cr.mm"
include "cpnf.mm"
include "wceq.mm"
include "wo.mm"
include "cxad.mm"
include "co.mm"
include "xrnemnf.mm"
include "caddc.mm"
include "rexadd.mm"
include "readdcl.mm"
include "eqeltrd.mm"
include "renemnfd.mm"
include "oveq2.mm"
include "rexr.mm"
include "renemnf.mm"
include "xaddpnf1.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "pnfnemnf.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "oveq1.mm"
include "xaddpnf2.mm"
include "sylan9eq.mm"
include "jaoian.mm"
include "sylanb.mm"

theorem xaddnemnf
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR* /\ A =/= -oo ) /\ ( B e. RR* /\ B =/= -oo ) ) -> ( A +e B ) =/= -oo )

  proof
    cA
    cxr
    wcel
    #
    cA
    cmnf
    wne
    #
    wa
    cA
    cr
    wcel
    #
    cA
    cpnf
    wceq
    #
    wo
    cB
    cxr
    wcel
    cB
    cmnf
    wne
    wa
    #
    cA
    cB
    cxad
    co
    #
    cmnf
    wne
    #
    cA
    xrnemnf
    @2
    @4
    @6
    @3
    @4
    @2
    cB
    cr
    wcel
    #
    cB
    cpnf
    wceq
    #
    wo
    @6
    cB
    xrnemnf
    @2
    @7
    @6
    @8
    @2
    @7
    wa
    #
    @5
    @9
    @5
    cA
    cB
    caddc
    co
    cr
    cA
    cB
    rexadd
    cA
    cB
    readdcl
    eqeltrd
    renemnfd
    @2
    @8
    wa
    #
    @5
    cpnf
    cmnf
    @8
    @2
    @5
    cA
    cpnf
    cxad
    co
    #
    cpnf
    cB
    cpnf
    cA
    cxad
    oveq2
    @2
    @0
    @1
    @11
    cpnf
    wceq
    cA
    rexr
    cA
    renemnf
    cA
    xaddpnf1
    syl2anc
    sylan9eqr
    cpnf
    cmnf
    wne
    #
    @10
    pnfnemnf
    a1i
    eqnetrd
    jaodan
    sylan2b
    @3
    @4
    wa
    #
    @5
    cpnf
    cmnf
    @3
    @4
    @5
    cpnf
    cB
    cxad
    co
    cpnf
    cA
    cpnf
    cB
    cxad
    oveq1
    cB
    xaddpnf2
    sylan9eq
    @12
    @13
    pnfnemnf
    a1i
    eqnetrd
    jaoian
    sylanb
end
