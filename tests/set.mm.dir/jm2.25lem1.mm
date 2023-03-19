include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cneg.mm"
include "wo.mm"
include "w3a.mm"
include "simpl1l.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "simpl1r.mm"
include "simpl3.mm"
include "simpr.mm"
include "acongtr.mm"
include "syl222anc.mm"
include "acongsym.mm"
include "syl31anc.mm"
include "impbida.mm"

theorem jm2.25lem1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) /\ ( A || ( C - D ) \/ A || ( C - -u D ) ) ) -> ( ( A || ( D - B ) \/ A || ( D - -u B ) ) <-> ( A || ( C - B ) \/ A || ( C - -u B ) ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cC
    cz
    wcel
    #
    cD
    cz
    wcel
    #
    wa
    #
    cA
    cC
    cD
    cmin
    co
    cdvds
    wbr
    cA
    cC
    cD
    cneg
    cmin
    co
    cdvds
    wbr
    wo
    #
    w3a
    #
    cA
    cD
    cB
    cmin
    co
    cdvds
    wbr
    cA
    cD
    cB
    cneg
    #
    cmin
    co
    cdvds
    wbr
    wo
    #
    cA
    cC
    cB
    cmin
    co
    cdvds
    wbr
    cA
    cC
    @8
    cmin
    co
    cdvds
    wbr
    wo
    #
    @7
    @9
    wa
    @0
    @3
    @4
    @1
    @6
    @9
    @10
    @0
    @1
    @5
    @6
    @9
    simpl1l
    @3
    @4
    @2
    @6
    @9
    simpl2l
    @3
    @4
    @2
    @6
    @9
    simpl2r
    @0
    @1
    @5
    @6
    @9
    simpl1r
    @2
    @5
    @6
    @9
    simpl3
    @7
    @9
    simpr
    cA
    cC
    cD
    cB
    acongtr
    syl222anc
    @7
    @10
    wa
    #
    @0
    @4
    @3
    @1
    cA
    cD
    cC
    cmin
    co
    cdvds
    wbr
    cA
    cD
    cC
    cneg
    cmin
    co
    cdvds
    wbr
    wo
    #
    @10
    @9
    @0
    @1
    @5
    @6
    @10
    simpl1l
    #
    @3
    @4
    @2
    @6
    @10
    simpl2r
    #
    @3
    @4
    @2
    @6
    @10
    simpl2l
    #
    @0
    @1
    @5
    @6
    @10
    simpl1r
    @11
    @0
    @3
    @4
    @6
    @12
    @13
    @15
    @14
    @2
    @5
    @6
    @10
    simpl3
    cA
    cC
    cD
    acongsym
    syl31anc
    @7
    @10
    simpr
    cA
    cD
    cC
    cB
    acongtr
    syl222anc
    impbida
end
