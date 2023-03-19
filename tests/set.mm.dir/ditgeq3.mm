include "wceq.mm"
include "cr.mm"
include "wral.mm"
include "cle.mm"
include "wbr.mm"
include "cioo.mm"
include "co.mm"
include "citg.mm"
include "cneg.mm"
include "cif.mm"
include "cdit.mm"
include "wss.mm"
include "wi.mm"
include "ioossre.mm"
include "ssralv.mm"
include "ax-mp.mm"
include "itgeq2.mm"
include "syl.mm"
include "negeqd.mm"
include "ifeq12d.mm"
include "df-ditg.mm"
include "3eqtr4g.mm"

theorem ditgeq3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cE: class E
  let cC: class C
  let wph: wff ph

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint ph x
  assert |- ( A. x e. RR D = E -> S_ [ A -> B ] D _d x = S_ [ A -> B ] E _d x )

  proof
    cD
    cE
    wceq
    #
    vx
    cr
    wral
    #
    cA
    cB
    cle
    wbr
    #
    vx
    cA
    cB
    cioo
    co
    #
    cD
    citg
    #
    vx
    cB
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
    @2
    vx
    @3
    cE
    citg
    #
    vx
    @5
    cE
    citg
    #
    cneg
    #
    cif
    vx
    cA
    cB
    cD
    cdit
    vx
    cA
    cB
    cE
    cdit
    @1
    @2
    @4
    @8
    @7
    @10
    @1
    @0
    vx
    @3
    wral
    #
    @4
    @8
    wceq
    @3
    cr
    wss
    @1
    @11
    wi
    cA
    cB
    ioossre
    @0
    vx
    @3
    cr
    ssralv
    ax-mp
    vx
    @3
    cD
    cE
    itgeq2
    syl
    @1
    @6
    @9
    @1
    @0
    vx
    @5
    wral
    #
    @6
    @9
    wceq
    @5
    cr
    wss
    @1
    @12
    wi
    cB
    cA
    ioossre
    @0
    vx
    @5
    cr
    ssralv
    ax-mp
    vx
    @5
    cD
    cE
    itgeq2
    syl
    negeqd
    ifeq12d
    vx
    cA
    cB
    cD
    df-ditg
    vx
    cA
    cB
    cE
    df-ditg
    3eqtr4g
end
