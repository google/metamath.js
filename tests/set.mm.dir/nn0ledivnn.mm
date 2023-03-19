include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "elnn0.mm"
include "wa.mm"
include "c1.mm"
include "nnge1.mm"
include "adantl.mm"
include "crp.mm"
include "wb.mm"
include "nnrp.mm"
include "nnledivrp.mm"
include "sylan2.mm"
include "mpbid.mm"
include "ex.mm"
include "cc.mm"
include "wne.mm"
include "nncn.mm"
include "nnne0.mm"
include "jca.mm"
include "div0.mm"
include "syl.mm"
include "0le0.mm"
include "syl6eqbr.mm"
include "oveq1.mm"
include "id.mm"
include "breq12d.mm"
include "adantr.mm"
include "mpbird.mm"
include "jaoi.mm"
include "sylbi.mm"
include "imp.mm"

theorem nn0ledivnn
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN0 /\ B e. NN ) -> ( A / B ) <_ A )

  proof
    cA
    cn0
    wcel
    #
    cB
    cn
    wcel
    #
    cA
    cB
    cdiv
    co
    #
    cA
    cle
    wbr
    #
    @0
    cA
    cn
    wcel
    #
    cA
    cc0
    wceq
    #
    wo
    @1
    @3
    wi
    #
    cA
    elnn0
    @4
    @6
    @5
    @4
    @1
    @3
    @4
    @1
    wa
    c1
    cB
    cle
    wbr
    #
    @3
    @1
    @7
    @4
    cB
    nnge1
    adantl
    @1
    @4
    cB
    crp
    wcel
    @7
    @3
    wb
    cB
    nnrp
    cA
    cB
    nnledivrp
    sylan2
    mpbid
    ex
    @5
    @1
    @3
    @5
    @1
    wa
    #
    @3
    cc0
    cB
    cdiv
    co
    #
    cc0
    cle
    wbr
    #
    @8
    @9
    cc0
    cc0
    cle
    @8
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
    @9
    cc0
    wceq
    @1
    @13
    @5
    @1
    @11
    @12
    cB
    nncn
    cB
    nnne0
    jca
    adantl
    cB
    div0
    syl
    0le0
    syl6eqbr
    @5
    @3
    @10
    wb
    @1
    @5
    @2
    @9
    cA
    cc0
    cle
    cA
    cc0
    cB
    cdiv
    oveq1
    @5
    id
    breq12d
    adantr
    mpbird
    ex
    jaoi
    sylbi
    imp
end
