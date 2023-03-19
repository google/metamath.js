include "cen.mm"
include "wbr.mm"
include "com.mm"
include "wcel.mm"
include "ccrd.mm"
include "cfv.mm"
include "carden2b.mm"
include "cardnn.mm"
include "sylan9eq.mm"

theorem cardennn
  let cA: class A
  let cB: class B


  assert |- ( ( A ~~ B /\ B e. _om ) -> ( card ` A ) = B )

  proof
    cA
    cB
    cen
    wbr
    cB
    com
    wcel
    cA
    ccrd
    cfv
    cB
    ccrd
    cfv
    cB
    cA
    cB
    carden2b
    cB
    cardnn
    sylan9eq
end
