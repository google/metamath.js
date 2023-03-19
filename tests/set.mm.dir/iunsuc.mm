include "csuc.mm"
include "ciun.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "df-suc.mm"
include "iuneq1.mm"
include "ax-mp.mm"
include "iunxun.mm"
include "iunxsn.mm"
include "uneq2i.mm"
include "3eqtri.mm"

theorem iunsuc
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume iunsuc.1: |- A e. _V
  assume iunsuc.2: |- ( x = A -> B = C )

  disjoint A x
  disjoint C x
  assert |- U_ x e. suc A B = ( U_ x e. A B u. C )

  proof
    vx
    cA
    csuc
    #
    cB
    ciun
    #
    vx
    cA
    cA
    csn
    #
    cun
    #
    cB
    ciun
    #
    vx
    cA
    cB
    ciun
    #
    vx
    @2
    cB
    ciun
    #
    cun
    @5
    cC
    cun
    @0
    @3
    wceq
    @1
    @4
    wceq
    cA
    df-suc
    vx
    @0
    @3
    cB
    iuneq1
    ax-mp
    vx
    cA
    @2
    cB
    iunxun
    @6
    cC
    @5
    vx
    cA
    cB
    cC
    iunsuc.1
    iunsuc.2
    iunxsn
    uneq2i
    3eqtri
end
