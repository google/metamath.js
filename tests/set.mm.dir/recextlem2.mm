include "cr.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wo.mm"
include "wceq.mm"
include "wn.mm"
include "oveq2.mm"
include "ax-icn.mm"
include "mul01i.mm"
include "syl6eq.mm"
include "oveq12.mm"
include "sylan2.mm"
include "00id.mm"
include "necon3ai.mm"
include "neorian.mm"
include "sylibr.mm"
include "cle.mm"
include "remulcl.mm"
include "anidms.mm"
include "anim12i.mm"
include "adantr.mm"
include "msqgt0.mm"
include "msqge0.mm"
include "an32s.mm"
include "addgtge0.mm"
include "syl2anc.mm"
include "anassrs.mm"
include "addgegt0.mm"
include "jaodan.mm"
include "3impa.mm"
include "gt0ne0d.mm"

theorem recextlem2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR /\ ( A + ( _i x. B ) ) =/= 0 ) -> ( ( A x. A ) + ( B x. B ) ) =/= 0 )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    ci
    cB
    cmul
    co
    #
    caddc
    co
    #
    cc0
    wne
    #
    w3a
    cA
    cA
    cmul
    co
    #
    cB
    cB
    cmul
    co
    #
    caddc
    co
    #
    @0
    @1
    @4
    cc0
    @7
    clt
    wbr
    #
    @4
    @0
    @1
    wa
    #
    cA
    cc0
    wne
    #
    cB
    cc0
    wne
    #
    wo
    #
    @8
    @4
    cA
    cc0
    wceq
    #
    cB
    cc0
    wceq
    #
    wa
    #
    wn
    @12
    @15
    @3
    cc0
    @15
    @3
    cc0
    cc0
    caddc
    co
    #
    cc0
    @14
    @13
    @2
    cc0
    wceq
    @3
    @16
    wceq
    @14
    @2
    ci
    cc0
    cmul
    co
    cc0
    cB
    cc0
    ci
    cmul
    oveq2
    ci
    ax-icn
    mul01i
    syl6eq
    cA
    cc0
    @2
    cc0
    caddc
    oveq12
    sylan2
    00id
    syl6eq
    necon3ai
    cA
    cc0
    cB
    cc0
    neorian
    sylibr
    @9
    @10
    @8
    @11
    @9
    @10
    wa
    @5
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    wa
    #
    cc0
    @5
    clt
    wbr
    #
    cc0
    @6
    cle
    wbr
    #
    wa
    #
    @8
    @9
    @19
    @10
    @0
    @17
    @1
    @18
    @0
    @17
    cA
    cA
    remulcl
    anidms
    @1
    @18
    cB
    cB
    remulcl
    anidms
    anim12i
    #
    adantr
    @0
    @10
    @1
    @22
    @0
    @10
    wa
    @20
    @1
    @21
    cA
    msqgt0
    cB
    msqge0
    anim12i
    an32s
    @5
    @6
    addgtge0
    syl2anc
    @9
    @11
    wa
    @19
    cc0
    @5
    cle
    wbr
    #
    cc0
    @6
    clt
    wbr
    #
    wa
    #
    @8
    @9
    @19
    @11
    @23
    adantr
    @0
    @1
    @11
    @26
    @0
    @24
    @1
    @11
    wa
    @25
    cA
    msqge0
    cB
    msqgt0
    anim12i
    anassrs
    @5
    @6
    addgegt0
    syl2anc
    jaodan
    sylan2
    3impa
    gt0ne0d
end
