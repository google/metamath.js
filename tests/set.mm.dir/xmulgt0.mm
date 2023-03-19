include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "cxmu.mm"
include "co.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "simpr.mm"
include "anim12i.mm"
include "cmul.mm"
include "mulgt0.mm"
include "an4s.mm"
include "ancoms.mm"
include "rexmul.mm"
include "adantl.mm"
include "breqtrrd.mm"
include "sylan.mm"
include "anassrs.mm"
include "0ltpnf.mm"
include "oveq2.mm"
include "xmulpnf1.mm"
include "adantr.mm"
include "sylan9eqr.mm"
include "syl5breqr.mm"
include "adantlr.mm"
include "simplrr.mm"
include "xmulasslem2.mm"
include "w3o.mm"
include "simprl.mm"
include "elxr.mm"
include "sylib.mm"
include "mpjao3dan.mm"
include "oveq1.mm"
include "xmulpnf2.mm"
include "simplr.mm"
include "simpll.mm"

theorem xmulgt0
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR* /\ 0 < A ) /\ ( B e. RR* /\ 0 < B ) ) -> 0 < ( A *e B ) )

  proof
    cA
    cxr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    cB
    cxr
    wcel
    #
    cc0
    cB
    clt
    wbr
    #
    wa
    #
    wa
    #
    cA
    cr
    wcel
    #
    cc0
    cA
    cB
    cxmu
    co
    #
    clt
    wbr
    #
    cA
    cpnf
    wceq
    #
    cA
    cmnf
    wceq
    #
    @6
    @7
    wa
    #
    cB
    cr
    wcel
    #
    @9
    cB
    cpnf
    wceq
    #
    cB
    cmnf
    wceq
    #
    @6
    @7
    @13
    @9
    @6
    @1
    @4
    wa
    #
    @7
    @13
    wa
    #
    @9
    @2
    @1
    @5
    @4
    @0
    @1
    simpr
    @3
    @4
    simpr
    anim12i
    @16
    @17
    wa
    cc0
    cA
    cB
    cmul
    co
    #
    @8
    clt
    @17
    @16
    cc0
    @18
    clt
    wbr
    #
    @7
    @1
    @13
    @4
    @19
    cA
    cB
    mulgt0
    an4s
    ancoms
    @17
    @8
    @18
    wceq
    @16
    cA
    cB
    rexmul
    adantl
    breqtrrd
    sylan
    anassrs
    @6
    @14
    @9
    @7
    @6
    @14
    wa
    cc0
    cpnf
    @8
    clt
    0ltpnf
    @14
    @6
    @8
    cA
    cpnf
    cxmu
    co
    #
    cpnf
    cB
    cpnf
    cA
    cxmu
    oveq2
    @2
    @20
    cpnf
    wceq
    @5
    cA
    xmulpnf1
    adantr
    sylan9eqr
    syl5breqr
    adantlr
    @12
    @4
    @15
    @9
    @2
    @3
    @4
    @7
    simplrr
    @9
    cB
    xmulasslem2
    sylan
    @6
    @13
    @14
    @15
    w3o
    #
    @7
    @6
    @3
    @21
    @2
    @3
    @4
    simprl
    cB
    elxr
    sylib
    adantr
    mpjao3dan
    @6
    @10
    wa
    cc0
    cpnf
    @8
    clt
    0ltpnf
    @10
    @6
    @8
    cpnf
    cB
    cxmu
    co
    #
    cpnf
    cA
    cpnf
    cB
    cxmu
    oveq1
    @5
    @22
    cpnf
    wceq
    @2
    cB
    xmulpnf2
    adantl
    sylan9eqr
    syl5breqr
    @6
    @1
    @11
    @9
    @0
    @1
    @5
    simplr
    @9
    cA
    xmulasslem2
    sylan
    @6
    @0
    @7
    @10
    @11
    w3o
    @0
    @1
    @5
    simpll
    cA
    elxr
    sylib
    mpjao3dan
end
