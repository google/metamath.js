include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cmo.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "caddc.mm"
include "cc.mm"
include "recn.mm"
include "npcan1.mm"
include "eqcomd.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "oveq1d.mm"
include "simpr.mm"
include "1mod.mm"
include "3adant1.mm"
include "oveq12d.mm"
include "crp.mm"
include "peano2rem.mm"
include "1red.mm"
include "simpl.mm"
include "0lt1.mm"
include "wi.mm"
include "0re.mm"
include "1re.mm"
include "lttr.mm"
include "mp3an12.mm"
include "mpani.mm"
include "imp.mm"
include "elrpd.mm"
include "3jca.mm"
include "modaddabs.mm"
include "0p1e1.mm"
include "oveq1i.mm"
include "syl5eq.mm"
include "3eqtr3d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "simp1.mm"
include "modcld.mm"
include "recnd.mm"
include "subidd.mm"
include "modsubmod.mm"
include "syl3anc.mm"
include "0mod.mm"
include "impbida.mm"

theorem m1mod0mod1
  let cA: class A
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR /\ N e. RR /\ 1 < N ) -> ( ( ( A - 1 ) mod N ) = 0 <-> ( A mod N ) = 1 ) )

  proof
    cA
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    c1
    cN
    clt
    wbr
    #
    w3a
    #
    cA
    c1
    cmin
    co
    #
    cN
    cmo
    co
    #
    cc0
    wceq
    #
    cA
    cN
    cmo
    co
    #
    c1
    wceq
    #
    @3
    @6
    wa
    #
    @7
    @4
    c1
    caddc
    co
    #
    cN
    cmo
    co
    #
    c1
    @9
    cA
    @10
    cN
    cmo
    @3
    cA
    @10
    wceq
    #
    @6
    @0
    @1
    @12
    @2
    @0
    cA
    cc
    wcel
    #
    @12
    cA
    recn
    @13
    @10
    cA
    cA
    npcan1
    eqcomd
    syl
    3ad2ant1
    adantr
    oveq1d
    @9
    @5
    c1
    cN
    cmo
    co
    #
    caddc
    co
    #
    cN
    cmo
    co
    #
    cc0
    c1
    caddc
    co
    #
    cN
    cmo
    co
    #
    @11
    c1
    @9
    @15
    @17
    cN
    cmo
    @9
    @5
    cc0
    @14
    c1
    caddc
    @3
    @6
    simpr
    @3
    @14
    c1
    wceq
    #
    @6
    @1
    @2
    @19
    @0
    cN
    1mod
    #
    3adant1
    adantr
    oveq12d
    oveq1d
    @9
    @4
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    cN
    crp
    wcel
    #
    w3a
    #
    @16
    @11
    wceq
    @3
    @24
    @6
    @3
    @21
    @22
    @23
    @0
    @1
    @21
    @2
    cA
    peano2rem
    3ad2ant1
    @3
    1red
    @1
    @2
    @23
    @0
    @1
    @2
    wa
    #
    cN
    @1
    @2
    simpl
    @1
    @2
    cc0
    cN
    clt
    wbr
    #
    @1
    cc0
    c1
    clt
    wbr
    #
    @2
    @26
    0lt1
    cc0
    cr
    wcel
    @22
    @1
    @27
    @2
    wa
    @26
    wi
    0re
    1re
    cc0
    c1
    cN
    lttr
    mp3an12
    mpani
    imp
    elrpd
    3adant1
    #
    3jca
    adantr
    @4
    c1
    cN
    modaddabs
    syl
    @3
    @18
    c1
    wceq
    #
    @6
    @1
    @2
    @29
    @0
    @25
    @18
    @14
    c1
    @17
    c1
    cN
    cmo
    0p1e1
    oveq1i
    @20
    syl5eq
    3adant1
    adantr
    3eqtr3d
    eqtrd
    @3
    @8
    wa
    #
    @5
    cA
    @7
    cmin
    co
    #
    cN
    cmo
    co
    #
    cc0
    @30
    @4
    @31
    cN
    cmo
    @30
    c1
    @7
    cA
    cmin
    @30
    @7
    c1
    @3
    @8
    simpr
    eqcomd
    oveq2d
    oveq1d
    @3
    @32
    cc0
    wceq
    @8
    @3
    @7
    @7
    cmin
    co
    #
    cN
    cmo
    co
    #
    cc0
    cN
    cmo
    co
    #
    @32
    cc0
    @3
    @33
    cc0
    cN
    cmo
    @3
    @7
    @3
    @7
    @3
    cA
    cN
    @0
    @1
    @2
    simp1
    #
    @28
    modcld
    #
    recnd
    subidd
    oveq1d
    @3
    @0
    @7
    cr
    wcel
    @23
    @34
    @32
    wceq
    @36
    @37
    @28
    cA
    @7
    cN
    modsubmod
    syl3anc
    @3
    @23
    @35
    cc0
    wceq
    @28
    cN
    0mod
    syl
    3eqtr3d
    adantr
    eqtrd
    impbida
end
