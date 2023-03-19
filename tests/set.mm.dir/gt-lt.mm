include "cgt.mm"
include "wbr.mm"
include "clt.mm"
include "ccnv.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "df-gt.mm"
include "breqi.mm"
include "brcnvg.mm"
include "syl5bb.mm"

theorem gt-lt
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. _V /\ B e. _V ) -> ( A > B <-> B < A ) )

  proof
    cA
    cB
    cgt
    wbr
    cA
    cB
    clt
    ccnv
    #
    wbr
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wa
    cB
    cA
    clt
    wbr
    cA
    cB
    cgt
    @0
    df-gt
    breqi
    cA
    cB
    cvv
    cvv
    clt
    brcnvg
    syl5bb
end
