include "csh.mm"
include "wcel.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "shub1.mm"
include "shjcom.mm"
include "sseqtrd.mm"

theorem shub2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. SH /\ B e. SH ) -> A C_ ( B vH A ) )

  proof
    cA
    csh
    wcel
    cB
    csh
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
    shub1
    cA
    cB
    shjcom
    sseqtrd
end
