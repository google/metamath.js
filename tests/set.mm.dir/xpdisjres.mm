include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cxp.mm"
include "cres.mm"
include "cvv.mm"
include "df-res.mm"
include "xpdisj1.mm"
include "syl5eq.mm"

theorem xpdisjres
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A i^i C ) = (/) -> ( ( A X. B ) |` C ) = (/) )

  proof
    cA
    cC
    cin
    c0
    wceq
    cA
    cB
    cxp
    #
    cC
    cres
    @0
    cC
    cvv
    cxp
    cin
    c0
    @0
    cC
    df-res
    cA
    cC
    cB
    cvv
    xpdisj1
    syl5eq
end
