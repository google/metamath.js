include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "wcel.mm"
include "cexp.mm"
include "co.mm"
include "cmo.mm"
include "wceq.mm"
include "cz.mm"
include "wa.mm"
include "wi.mm"
include "dvdszrcl.mm"
include "w3a.mm"
include "cc0.mm"
include "dvdsmod0.mm"
include "3ad2antl2.mm"
include "ex.mm"
include "simpl3.mm"
include "0expd.mm"
include "oveq1d.mm"
include "cn0.mm"
include "crp.mm"
include "simpl1.mm"
include "0zd.mm"
include "nnnn0.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "nnrp.mm"
include "3ad2ant2.mm"
include "simpr.mm"
include "0mod.mm"
include "syl.mm"
include "eqtr4d.mm"
include "modexp.mm"
include "syl221anc.mm"
include "3eqtr4d.mm"
include "syld.mm"
include "3exp.mm"
include "com24.mm"
include "adantl.mm"
include "mpcom.mm"
include "3imp31.mm"

theorem dvdsmodexp
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( N e. NN /\ B e. NN /\ N || A ) -> ( ( A ^ B ) mod N ) = ( A mod N ) )

  proof
    cN
    cA
    cdvds
    wbr
    #
    cB
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    cA
    cB
    cexp
    co
    cN
    cmo
    co
    #
    cA
    cN
    cmo
    co
    #
    wceq
    #
    cN
    cz
    wcel
    #
    cA
    cz
    wcel
    #
    wa
    @0
    @1
    @2
    @5
    wi
    wi
    #
    cN
    cA
    dvdszrcl
    @7
    @0
    @8
    wi
    @6
    @7
    @2
    @1
    @0
    @5
    @7
    @2
    @1
    @0
    @5
    wi
    @7
    @2
    @1
    w3a
    #
    @0
    @4
    cc0
    wceq
    #
    @5
    @9
    @0
    @10
    @2
    @7
    @0
    @10
    @1
    cN
    cA
    dvdsmod0
    3ad2antl2
    ex
    @9
    @10
    @5
    @9
    @10
    wa
    #
    cc0
    cB
    cexp
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
    @3
    @4
    @11
    @12
    cc0
    cN
    cmo
    @11
    cB
    @7
    @2
    @1
    @10
    simpl3
    0expd
    oveq1d
    @11
    @7
    cc0
    cz
    wcel
    cB
    cn0
    wcel
    #
    cN
    crp
    wcel
    #
    @4
    @14
    wceq
    @3
    @13
    wceq
    @7
    @2
    @1
    @10
    simpl1
    @11
    0zd
    @9
    @15
    @10
    @1
    @7
    @15
    @2
    cB
    nnnn0
    3ad2ant3
    adantr
    @9
    @16
    @10
    @2
    @7
    @16
    @1
    cN
    nnrp
    3ad2ant2
    adantr
    #
    @11
    @4
    cc0
    @14
    @9
    @10
    simpr
    @11
    @16
    @14
    cc0
    wceq
    @17
    cN
    0mod
    syl
    eqtr4d
    #
    cA
    cc0
    cB
    cN
    modexp
    syl221anc
    @18
    3eqtr4d
    ex
    syld
    3exp
    com24
    adantl
    mpcom
    3imp31
end
