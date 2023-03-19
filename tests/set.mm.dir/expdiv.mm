include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cn0.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cexp.mm"
include "c1.mm"
include "cmul.mm"
include "wceq.mm"
include "divrec.mm"
include "3expb.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "reccl.mm"
include "mulexp.mm"
include "syl3an2.mm"
include "cz.mm"
include "simp2l.mm"
include "simp2r.mm"
include "nn0z.mm"
include "3ad2ant3.mm"
include "exprec.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "expcl.mm"
include "3adant2.mm"
include "adantlr.mm"
include "3adant1.mm"
include "expne0i.mm"
include "divrecd.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"

theorem expdiv
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( A e. CC /\ ( B e. CC /\ B =/= 0 ) /\ N e. NN0 ) -> ( ( A / B ) ^ N ) = ( ( A ^ N ) / ( B ^ N ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cA
    cB
    cdiv
    co
    #
    cN
    cexp
    co
    cA
    c1
    cB
    cdiv
    co
    #
    cmul
    co
    #
    cN
    cexp
    co
    #
    cA
    cN
    cexp
    co
    #
    @7
    cN
    cexp
    co
    #
    cmul
    co
    #
    @10
    cB
    cN
    cexp
    co
    #
    cdiv
    co
    #
    @5
    @6
    @8
    cN
    cexp
    @0
    @3
    @6
    @8
    wceq
    #
    @4
    @0
    @1
    @2
    @15
    cA
    cB
    divrec
    3expb
    3adant3
    oveq1d
    @3
    @0
    @7
    cc
    wcel
    @4
    @9
    @12
    wceq
    cB
    reccl
    cA
    @7
    cN
    mulexp
    syl3an2
    @5
    @12
    @10
    c1
    @13
    cdiv
    co
    #
    cmul
    co
    @14
    @5
    @11
    @16
    @10
    cmul
    @5
    @1
    @2
    cN
    cz
    wcel
    #
    @11
    @16
    wceq
    @0
    @1
    @2
    @4
    simp2l
    #
    @0
    @1
    @2
    @4
    simp2r
    #
    @4
    @0
    @17
    @3
    cN
    nn0z
    3ad2ant3
    #
    cB
    cN
    exprec
    syl3anc
    oveq2d
    @5
    @10
    @13
    @0
    @4
    @10
    cc
    wcel
    @3
    cA
    cN
    expcl
    3adant2
    @3
    @4
    @13
    cc
    wcel
    #
    @0
    @1
    @4
    @21
    @2
    cB
    cN
    expcl
    adantlr
    3adant1
    @5
    @1
    @2
    @17
    @13
    cc0
    wne
    @18
    @19
    @20
    cB
    cN
    expne0i
    syl3anc
    divrecd
    eqtr4d
    3eqtrd
end
