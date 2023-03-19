include "word.mm"
include "wcel.mm"
include "wa.mm"
include "ordirr.mm"
include "wtr.mm"
include "wi.mm"
include "ordtr.mm"
include "trel.mm"
include "syl.mm"
include "mtod.mm"

theorem ordn2lp
  let cA: class A
  let cB: class B


  assert |- ( Ord A -> -. ( A e. B /\ B e. A ) )

  proof
    cA
    word
    #
    cA
    cB
    wcel
    cB
    cA
    wcel
    wa
    #
    cA
    cA
    wcel
    #
    cA
    ordirr
    @0
    cA
    wtr
    @1
    @2
    wi
    cA
    ordtr
    cA
    cA
    cB
    trel
    syl
    mtod
end
