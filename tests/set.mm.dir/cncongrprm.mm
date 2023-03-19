include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cprime.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cn.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cmul.mm"
include "cmo.mm"
include "wb.mm"
include "prmnn.mm"
include "ad2antrl.mm"
include "wi.mm"
include "coprm.mm"
include "prmz.mm"
include "gcdcom.mm"
include "sylan.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "ancoms.mm"
include "biimpd.mm"
include "expimpd.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "jca.mm"
include "cncongrcoprm.mm"
include "syldan.mm"

theorem cncongrprm
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P


  assert |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\ ( P e. Prime /\ -. P || C ) ) -> ( ( ( A x. C ) mod P ) = ( ( B x. C ) mod P ) <-> ( A mod P ) = ( B mod P ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cC
    cz
    wcel
    #
    w3a
    #
    cP
    cprime
    wcel
    #
    cP
    cC
    cdvds
    wbr
    wn
    #
    wa
    #
    cP
    cn
    wcel
    #
    cC
    cP
    cgcd
    co
    #
    c1
    wceq
    #
    wa
    cA
    cC
    cmul
    co
    cP
    cmo
    co
    cB
    cC
    cmul
    co
    cP
    cmo
    co
    wceq
    cA
    cP
    cmo
    co
    cB
    cP
    cmo
    co
    wceq
    wb
    @3
    @6
    wa
    @7
    @9
    @4
    @7
    @3
    @5
    cP
    prmnn
    ad2antrl
    @3
    @6
    @9
    @2
    @0
    @6
    @9
    wi
    @1
    @2
    @4
    @5
    @9
    @2
    @4
    wa
    @5
    @9
    @4
    @2
    @5
    @9
    wb
    @4
    @2
    wa
    #
    @5
    cP
    cC
    cgcd
    co
    #
    c1
    wceq
    @9
    cP
    cC
    coprm
    @10
    @11
    @8
    c1
    @4
    cP
    cz
    wcel
    @2
    @11
    @8
    wceq
    cP
    prmz
    cP
    cC
    gcdcom
    sylan
    eqeq1d
    bitrd
    ancoms
    biimpd
    expimpd
    3ad2ant3
    imp
    jca
    cA
    cB
    cC
    cP
    cncongrcoprm
    syldan
end
