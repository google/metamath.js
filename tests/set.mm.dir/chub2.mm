include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "chub1.mm"
include "chjcom.mm"
include "sseqtrd.mm"

theorem chub2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> A C_ ( B vH A ) )

  proof
    cA
    cch
    wcel
    cB
    cch
    wcel
    wa
    cA
    cA
    cB
    chj
    co
    cB
    cA
    chj
    co
    cA
    cB
    chub1
    cA
    cB
    chjcom
    sseqtrd
end
