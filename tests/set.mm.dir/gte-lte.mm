include "cge-real.mm"
include "wbr.mm"
include "cle.mm"
include "ccnv.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "df-gte.mm"
include "breqi.mm"
include "brcnvg.mm"
include "syl5bb.mm"

theorem gte-lte
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. _V /\ B e. _V ) -> ( A >_ B <-> B <_ A ) )

  proof
    cA
    cB
    cge-real
    wbr
    cA
    cB
    cle
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
    cle
    wbr
    cA
    cB
    cge-real
    @0
    df-gte
    breqi
    cA
    cB
    cvv
    cvv
    cle
    brcnvg
    syl5bb
end
