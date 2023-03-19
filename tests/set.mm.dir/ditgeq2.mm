include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cioo.mm"
include "co.mm"
include "citg.mm"
include "cneg.mm"
include "cif.mm"
include "cdit.mm"
include "breq2.mm"
include "oveq2.mm"
include "itgeq1.mm"
include "syl.mm"
include "oveq1.mm"
include "negeqd.mm"
include "ifbieq12d.mm"
include "df-ditg.mm"
include "3eqtr4g.mm"

theorem ditgeq2
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
  assert |- ( A = B -> S_ [ C -> A ] D _d x = S_ [ C -> B ] D _d x )

  proof
    cA
    cB
    wceq
    #
    cC
    cA
    cle
    wbr
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
    vx
    cA
    cC
    cioo
    co
    #
    cD
    citg
    #
    cneg
    #
    cif
    cC
    cB
    cle
    wbr
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
    vx
    cB
    cC
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
    cC
    cA
    cD
    cdit
    vx
    cC
    cB
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
    breq2
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
    oveq2
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
    oveq1
    vx
    @4
    @10
    cD
    itgeq1
    syl
    negeqd
    ifbieq12d
    vx
    cC
    cA
    cD
    df-ditg
    vx
    cC
    cB
    cD
    df-ditg
    3eqtr4g
end
