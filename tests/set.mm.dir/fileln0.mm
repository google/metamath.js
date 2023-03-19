include "wcel.mm"
include "c0.mm"
include "wn.mm"
include "wne.mm"
include "cfil.mm"
include "cfv.mm"
include "id.mm"
include "0nelfil.mm"
include "nelne2.mm"
include "syl2anr.mm"

theorem fileln0
  let cA: class A
  let cF: class F
  let cX: class X


  assert |- ( ( F e. ( Fil ` X ) /\ A e. F ) -> A =/= (/) )

  proof
    cA
    cF
    wcel
    #
    @0
    c0
    cF
    wcel
    wn
    cA
    c0
    wne
    cF
    cX
    cfil
    cfv
    wcel
    @0
    id
    cF
    cX
    0nelfil
    cA
    c0
    cF
    nelne2
    syl2anr
end
