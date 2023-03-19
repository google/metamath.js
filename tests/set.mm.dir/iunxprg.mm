include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "ciun.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "df-pr.mm"
include "iuneq1.mm"
include "ax-mp.mm"
include "iunxun.mm"
include "eqtri.mm"
include "iunxsng.mm"
include "adantr.mm"
include "adantl.mm"
include "uneq12d.mm"
include "syl5eq.mm"

theorem iunxprg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cV: class V
  let cW: class W
  assume iunxprg.1: |- ( x = A -> C = D )
  assume iunxprg.2: |- ( x = B -> C = E )

  disjoint A x
  disjoint B x
  disjoint D x
  disjoint E x
  assert |- ( ( A e. V /\ B e. W ) -> U_ x e. { A , B } C = ( D u. E ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    vx
    cA
    cB
    cpr
    #
    cC
    ciun
    #
    vx
    cA
    csn
    #
    cC
    ciun
    #
    vx
    cB
    csn
    #
    cC
    ciun
    #
    cun
    #
    cD
    cE
    cun
    @4
    vx
    @5
    @7
    cun
    #
    cC
    ciun
    #
    @9
    @3
    @10
    wceq
    @4
    @11
    wceq
    cA
    cB
    df-pr
    vx
    @3
    @10
    cC
    iuneq1
    ax-mp
    vx
    @5
    @7
    cC
    iunxun
    eqtri
    @2
    @6
    cD
    @8
    cE
    @0
    @6
    cD
    wceq
    @1
    vx
    cA
    cC
    cD
    cV
    iunxprg.1
    iunxsng
    adantr
    @1
    @8
    cE
    wceq
    @0
    vx
    cB
    cC
    cE
    cW
    iunxprg.2
    iunxsng
    adantl
    uneq12d
    syl5eq
end
