include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "chsh.mm"
include "shjcom.mm"
include "syl2an.mm"

theorem chjcom
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A vH B ) = ( B vH A ) )

  proof
    cA
    cch
    wcel
    cA
    csh
    wcel
    cB
    csh
    wcel
    cA
    cB
    chj
    co
    cB
    cA
    chj
    co
    wceq
    cB
    cch
    wcel
    cA
    chsh
    cB
    chsh
    cA
    cB
    shjcom
    syl2an
end
