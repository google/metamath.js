include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "clt.mm"
include "wceq.mm"
include "modcl.mm"
include "anim1i.mm"
include "3impa.mm"
include "adantr.mm"
include "modge0.mm"
include "3adant3.mm"
include "rpre.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "modlt.mm"
include "simpr.mm"
include "ltletrd.mm"
include "modid.mm"
include "syl12anc.mm"

theorem modabs
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR /\ B e. RR+ /\ C e. RR+ ) /\ B <_ C ) -> ( ( A mod B ) mod C ) = ( A mod B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    cC
    crp
    wcel
    #
    w3a
    #
    cB
    cC
    cle
    wbr
    #
    wa
    #
    cA
    cB
    cmo
    co
    #
    cr
    wcel
    #
    @2
    wa
    #
    cc0
    @6
    cle
    wbr
    #
    @6
    cC
    clt
    wbr
    @6
    cC
    cmo
    co
    @6
    wceq
    @3
    @8
    @4
    @0
    @1
    @2
    @8
    @0
    @1
    wa
    @7
    @2
    cA
    cB
    modcl
    #
    anim1i
    3impa
    adantr
    @3
    @9
    @4
    @0
    @1
    @9
    @2
    cA
    cB
    modge0
    3adant3
    adantr
    @5
    @6
    cB
    cC
    @3
    @7
    @4
    @0
    @1
    @7
    @2
    @10
    3adant3
    adantr
    @3
    cB
    cr
    wcel
    #
    @4
    @1
    @0
    @11
    @2
    cB
    rpre
    3ad2ant2
    adantr
    @3
    cC
    cr
    wcel
    #
    @4
    @2
    @0
    @12
    @1
    cC
    rpre
    3ad2ant3
    adantr
    @3
    @6
    cB
    clt
    wbr
    #
    @4
    @0
    @1
    @13
    @2
    cA
    cB
    modlt
    3adant3
    adantr
    @3
    @4
    simpr
    ltletrd
    @6
    cC
    modid
    syl12anc
end
