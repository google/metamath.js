include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cioo.mm"
include "co.mm"
include "citg.mm"
include "cneg.mm"
include "cif.mm"
include "cdit.mm"
include "breq1.mm"
include "oveq1.mm"
include "itgeq1.mm"
include "syl.mm"
include "oveq2.mm"
include "negeqd.mm"
include "ifbieq12d.mm"
include "df-ditg.mm"
include "3eqtr4g.mm"

theorem ditgeq1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let wph: wff ph

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint ph x
  assert |- ( A = B -> S_ [ A -> C ] D _d x = S_ [ B -> C ] D _d x )

  proof
    cA
    cB
    wceq
    #
    cA
    cC
    cle
    wbr
    #
    vx
    cA
    cC
    cioo
    co
    #
    cD
    citg
    #
    vx
    cC
    cA
    cioo
    co
    #
    cD
    citg
    #
    cneg
    #
    cif
    cB
    cC
    cle
    wbr
    #
    vx
    cB
    cC
    cioo
    co
    #
    cD
    citg
    #
    vx
    cC
    cB
    cioo
    co
    #
    cD
    citg
    #
    cneg
    #
    cif
    vx
    cA
    cC
    cD
    cdit
    vx
    cB
    cC
    cD
    cdit
    @0
    @1
    @7
    @3
    @6
    @9
    @12
    cA
    cB
    cC
    cle
    breq1
    @0
    @2
    @8
    wceq
    @3
    @9
    wceq
    cA
    cB
    cC
    cioo
    oveq1
    vx
    @2
    @8
    cD
    itgeq1
    syl
    @0
    @5
    @11
    @0
    @4
    @10
    wceq
    @5
    @11
    wceq
    cA
    cB
    cC
    cioo
    oveq2
    vx
    @4
    @10
    cD
    itgeq1
    syl
    negeqd
    ifbieq12d
    vx
    cA
    cC
    cD
    df-ditg
    vx
    cB
    cC
    cD
    df-ditg
    3eqtr4g
end
