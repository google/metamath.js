include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "w3a.mm"
include "c2.mm"
include "cexp.mm"
include "cmul.mm"
include "clgs.mm"
include "zsqcl.mm"
include "adantr.mm"
include "simpl.mm"
include "3anim123i.mm"
include "cc.mm"
include "wb.mm"
include "zcn.mm"
include "sqne0.mm"
include "syl.mm"
include "biimpar.mm"
include "simpr.mm"
include "anim12i.mm"
include "3adant3.mm"
include "lgsdir.mm"
include "syl2anc.mm"
include "3anass.mm"
include "biimpri.mm"
include "3adant2.mm"
include "lgssq.mm"
include "oveq1d.mm"
include "3adant1.mm"
include "lgscl.mm"
include "zcnd.mm"
include "mulid2d.mm"
include "3eqtrd.mm"

theorem lgsmulsqcoprm
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( ( A e. ZZ /\ A =/= 0 ) /\ ( B e. ZZ /\ B =/= 0 ) /\ ( N e. ZZ /\ ( A gcd N ) = 1 ) ) -> ( ( ( A ^ 2 ) x. B ) /L N ) = ( B /L N ) )

  proof
    cA
    cz
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cB
    cz
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    cN
    cz
    wcel
    #
    cA
    cN
    cgcd
    co
    c1
    wceq
    #
    wa
    #
    w3a
    #
    cA
    c2
    cexp
    co
    #
    cB
    cmul
    co
    cN
    clgs
    co
    #
    @10
    cN
    clgs
    co
    #
    cB
    cN
    clgs
    co
    #
    cmul
    co
    #
    c1
    @13
    cmul
    co
    @13
    @9
    @10
    cz
    wcel
    #
    @3
    @6
    w3a
    @10
    cc0
    wne
    #
    @4
    wa
    #
    @11
    @14
    wceq
    @2
    @15
    @5
    @3
    @8
    @6
    @0
    @15
    @1
    cA
    zsqcl
    adantr
    @3
    @4
    simpl
    #
    @6
    @7
    simpl
    #
    3anim123i
    @2
    @5
    @17
    @8
    @2
    @16
    @5
    @4
    @0
    @16
    @1
    @0
    cA
    cc
    wcel
    @16
    @1
    wb
    cA
    zcn
    cA
    sqne0
    syl
    biimpar
    @3
    @4
    simpr
    anim12i
    3adant3
    @10
    cB
    cN
    lgsdir
    syl2anc
    @9
    @12
    c1
    @13
    cmul
    @9
    @2
    @6
    @7
    w3a
    #
    @12
    c1
    wceq
    @2
    @8
    @20
    @5
    @20
    @2
    @8
    wa
    @2
    @6
    @7
    3anass
    biimpri
    3adant2
    cA
    cN
    lgssq
    syl
    oveq1d
    @9
    @13
    @9
    @13
    @9
    @3
    @6
    wa
    #
    @13
    cz
    wcel
    @5
    @8
    @21
    @2
    @5
    @3
    @8
    @6
    @18
    @19
    anim12i
    3adant1
    cB
    cN
    lgscl
    syl
    zcnd
    mulid2d
    3eqtrd
end
