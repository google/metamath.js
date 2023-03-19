include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "wne.mm"
include "wa.mm"
include "cr.mm"
include "cmnf.mm"
include "wceq.mm"
include "wo.mm"
include "cxad.mm"
include "co.mm"
include "xrnepnf.mm"
include "caddc.mm"
include "rexadd.mm"
include "readdcl.mm"
include "eqeltrd.mm"
include "renepnfd.mm"
include "oveq2.mm"
include "rexr.mm"
include "renepnf.mm"
include "xaddmnf1.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "mnfnepnf.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "oveq1.mm"
include "xaddmnf2.mm"
include "sylan9eq.mm"
include "jaoian.mm"
include "sylanb.mm"

theorem xaddnepnf
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR* /\ A =/= +oo ) /\ ( B e. RR* /\ B =/= +oo ) ) -> ( A +e B ) =/= +oo )

  proof
    cA
    cxr
    wcel
    #
    cA
    cpnf
    wne
    #
    wa
    cA
    cr
    wcel
    #
    cA
    cmnf
    wceq
    #
    wo
    cB
    cxr
    wcel
    cB
    cpnf
    wne
    wa
    #
    cA
    cB
    cxad
    co
    #
    cpnf
    wne
    #
    cA
    xrnepnf
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
    cmnf
    wceq
    #
    wo
    @6
    cB
    xrnepnf
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
    renepnfd
    @2
    @8
    wa
    #
    @5
    cmnf
    cpnf
    @8
    @2
    @5
    cA
    cmnf
    cxad
    co
    #
    cmnf
    cB
    cmnf
    cA
    cxad
    oveq2
    @2
    @0
    @1
    @11
    cmnf
    wceq
    cA
    rexr
    cA
    renepnf
    cA
    xaddmnf1
    syl2anc
    sylan9eqr
    cmnf
    cpnf
    wne
    #
    @10
    mnfnepnf
    a1i
    eqnetrd
    jaodan
    sylan2b
    @3
    @4
    wa
    #
    @5
    cmnf
    cpnf
    @3
    @4
    @5
    cmnf
    cB
    cxad
    co
    cmnf
    cA
    cmnf
    cB
    cxad
    oveq1
    cB
    xaddmnf2
    sylan9eq
    @12
    @13
    mnfnepnf
    a1i
    eqnetrd
    jaoian
    sylanb
end
