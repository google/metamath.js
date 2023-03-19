include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "cle.mm"
include "readdcl.mm"
include "3adant3.mm"
include "anidms.mm"
include "3ad2ant3.mm"
include "2re.mm"
include "remulcl.mm"
include "mpan.mm"
include "3jca.mm"
include "adantr.mm"
include "id.mm"
include "jca.mm"
include "simpr.mm"
include "lt2add.mm"
include "sylc.mm"
include "recn.mm"
include "2timesd.mm"
include "leidd.mm"
include "eqbrtrrd.mm"
include "ltletr.mm"
include "ex.mm"

theorem 2leaddle2
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( ( A < C /\ B < C ) -> ( A + B ) < ( 2 x. C ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    w3a
    #
    cA
    cC
    clt
    wbr
    cB
    cC
    clt
    wbr
    wa
    #
    cA
    cB
    caddc
    co
    #
    c2
    cC
    cmul
    co
    #
    clt
    wbr
    #
    @3
    @4
    wa
    #
    @5
    cr
    wcel
    #
    cC
    cC
    caddc
    co
    #
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    w3a
    #
    @5
    @10
    clt
    wbr
    #
    @10
    @6
    cle
    wbr
    #
    wa
    @7
    @3
    @13
    @4
    @3
    @9
    @11
    @12
    @0
    @1
    @9
    @2
    cA
    cB
    readdcl
    3adant3
    @2
    @0
    @11
    @1
    @2
    @11
    cC
    cC
    readdcl
    anidms
    3ad2ant3
    @2
    @0
    @12
    @1
    c2
    cr
    wcel
    @2
    @12
    2re
    c2
    cC
    remulcl
    mpan
    #
    3ad2ant3
    3jca
    adantr
    @8
    @14
    @15
    @8
    @0
    @1
    wa
    #
    @2
    @2
    wa
    #
    wa
    #
    @4
    @14
    @3
    @19
    @4
    @3
    @17
    @18
    @0
    @1
    @17
    @2
    @17
    id
    3adant3
    @2
    @0
    @18
    @1
    @2
    @2
    @2
    @2
    id
    #
    @20
    jca
    3ad2ant3
    jca
    adantr
    @3
    @4
    simpr
    cA
    cB
    cC
    cC
    lt2add
    sylc
    @3
    @15
    @4
    @2
    @0
    @15
    @1
    @2
    @6
    @10
    @6
    cle
    @2
    cC
    cC
    recn
    2timesd
    @2
    @6
    @16
    leidd
    eqbrtrrd
    3ad2ant3
    adantr
    jca
    @5
    @10
    @6
    ltletr
    sylc
    ex
end
