include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "crp.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "cc.mm"
include "recn.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "simpl2.mm"
include "simpr.mm"
include "modcld.mm"
include "recnd.mm"
include "zcn.mm"
include "3ad2ant3.mm"
include "mulcld.mm"
include "addcomd.mm"
include "oveq1d.mm"
include "wceq.mm"
include "zre.mm"
include "remulcld.mm"
include "simpl.mm"
include "adantl.mm"
include "3adant1.mm"
include "simp1.mm"
include "anim1i.mm"
include "simpl3.mm"
include "modmulmod.mm"
include "syl3anc.mm"
include "remulcl.mm"
include "sylan2.mm"
include "modabs2.mm"
include "sylan.mm"
include "eqtr4d.mm"
include "modadd1.mm"
include "syl211anc.mm"
include "modaddmod.mm"
include "mulcl.mm"
include "syl2an.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem modaddmulmod
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M


  assert |- ( ( ( A e. RR /\ B e. RR /\ C e. ZZ ) /\ M e. RR+ ) -> ( ( A + ( ( B mod M ) x. C ) ) mod M ) = ( ( A + ( B x. C ) ) mod M ) )

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
    cz
    wcel
    #
    w3a
    #
    cM
    crp
    wcel
    #
    wa
    #
    cA
    cB
    cM
    cmo
    co
    #
    cC
    cmul
    co
    #
    caddc
    co
    #
    cM
    cmo
    co
    @7
    cA
    caddc
    co
    #
    cM
    cmo
    co
    #
    cB
    cC
    cmul
    co
    #
    cM
    cmo
    co
    #
    cA
    caddc
    co
    cM
    cmo
    co
    #
    cA
    @11
    caddc
    co
    #
    cM
    cmo
    co
    #
    @5
    @8
    @9
    cM
    cmo
    @5
    cA
    @7
    @3
    cA
    cc
    wcel
    #
    @4
    @0
    @1
    @16
    @2
    cA
    recn
    3ad2ant1
    #
    adantr
    @5
    @6
    cC
    @5
    @6
    @5
    cB
    cM
    @0
    @1
    @2
    @4
    simpl2
    #
    @3
    @4
    simpr
    #
    modcld
    #
    recnd
    @3
    cC
    cc
    wcel
    #
    @4
    @2
    @0
    @21
    @1
    cC
    zcn
    #
    3ad2ant3
    adantr
    mulcld
    addcomd
    oveq1d
    @5
    @7
    cr
    wcel
    @12
    cr
    wcel
    @0
    @4
    wa
    @7
    cM
    cmo
    co
    #
    @12
    cM
    cmo
    co
    #
    wceq
    @10
    @13
    wceq
    @5
    @6
    cC
    @20
    @3
    cC
    cr
    wcel
    #
    @4
    @2
    @0
    @25
    @1
    cC
    zre
    #
    3ad2ant3
    adantr
    remulcld
    @5
    @11
    cM
    @3
    @11
    cr
    wcel
    #
    @4
    @1
    @2
    @27
    @0
    @1
    @2
    wa
    cB
    cC
    @1
    @2
    simpl
    @2
    @25
    @1
    @26
    adantl
    remulcld
    3adant1
    adantr
    @19
    modcld
    @3
    @0
    @4
    @0
    @1
    @2
    simp1
    #
    anim1i
    @5
    @23
    @12
    @24
    @5
    @1
    @2
    @4
    @23
    @12
    wceq
    @18
    @0
    @1
    @2
    @4
    simpl3
    @19
    cB
    cC
    cM
    modmulmod
    syl3anc
    @3
    @27
    @4
    @24
    @12
    wceq
    @1
    @2
    @27
    @0
    @2
    @1
    @25
    @27
    @26
    cB
    cC
    remulcl
    sylan2
    3adant1
    #
    @11
    cM
    modabs2
    sylan
    eqtr4d
    @7
    @12
    cA
    cM
    modadd1
    syl211anc
    @5
    @13
    @11
    cA
    caddc
    co
    #
    cM
    cmo
    co
    #
    @15
    @5
    @27
    @0
    @4
    @13
    @31
    wceq
    @3
    @27
    @4
    @29
    adantr
    @3
    @0
    @4
    @28
    adantr
    @19
    @11
    cA
    cM
    modaddmod
    syl3anc
    @5
    @30
    @14
    cM
    cmo
    @3
    @30
    @14
    wceq
    @4
    @3
    @11
    cA
    @1
    @2
    @11
    cc
    wcel
    #
    @0
    @1
    cB
    cc
    wcel
    @21
    @32
    @2
    cB
    recn
    @22
    cB
    cC
    mulcl
    syl2an
    3adant1
    @17
    addcomd
    adantr
    oveq1d
    eqtrd
    3eqtrd
end
