include "cn.mm"
include "wcel.mm"
include "cc.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "wa.mm"
include "cmul.mm"
include "nnmulcl.mm"
include "c1.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "nncn.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "nnne0.mm"
include "jca.mm"
include "3ad2ant1.mm"
include "divmul24.mm"
include "syl22anc.mm"
include "dividd.mm"
include "oveq1d.mm"
include "divcl.mm"
include "3expb.mm"
include "sylan2.mm"
include "ancoms.mm"
include "mulid2d.mm"
include "3adant2.mm"
include "3eqtrd.mm"
include "eleq1d.mm"
include "syl5ib.mm"
include "imp.mm"

theorem nndivtr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. NN /\ B e. NN /\ C e. CC ) /\ ( ( B / A ) e. NN /\ ( C / B ) e. NN ) ) -> ( C / A ) e. NN )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    cC
    cc
    wcel
    #
    w3a
    #
    cB
    cA
    cdiv
    co
    #
    cn
    wcel
    cC
    cB
    cdiv
    co
    #
    cn
    wcel
    wa
    #
    cC
    cA
    cdiv
    co
    #
    cn
    wcel
    #
    @6
    @4
    @5
    cmul
    co
    #
    cn
    wcel
    @3
    @8
    @4
    @5
    nnmulcl
    @3
    @9
    @7
    cn
    @3
    @9
    cB
    cB
    cdiv
    co
    #
    @7
    cmul
    co
    #
    c1
    @7
    cmul
    co
    #
    @7
    @3
    cB
    cc
    wcel
    #
    @2
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    @13
    cB
    cc0
    wne
    #
    wa
    #
    @9
    @11
    wceq
    @1
    @0
    @13
    @2
    cB
    nncn
    #
    3ad2ant2
    @0
    @1
    @2
    simp3
    @0
    @1
    @16
    @2
    @0
    @14
    @15
    cA
    nncn
    cA
    nnne0
    jca
    #
    3ad2ant1
    @1
    @0
    @18
    @2
    @1
    @13
    @17
    @19
    cB
    nnne0
    #
    jca
    3ad2ant2
    cB
    cC
    cA
    cB
    divmul24
    syl22anc
    @1
    @0
    @11
    @12
    wceq
    @2
    @1
    @10
    c1
    @7
    cmul
    @1
    cB
    @19
    @21
    dividd
    oveq1d
    3ad2ant2
    @0
    @2
    @12
    @7
    wceq
    @1
    @0
    @2
    wa
    @7
    @2
    @0
    @7
    cc
    wcel
    #
    @0
    @2
    @16
    @22
    @20
    @2
    @14
    @15
    @22
    cC
    cA
    divcl
    3expb
    sylan2
    ancoms
    mulid2d
    3adant2
    3eqtrd
    eleq1d
    syl5ib
    imp
end
