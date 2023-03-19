include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "chj.mm"
include "co.mm"
include "wss.mm"
include "chsh.mm"
include "shub1.mm"
include "syl2an.mm"

theorem chub1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> A C_ ( A vH B ) )

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
    cA
    cB
    chj
    co
    wss
    cB
    cch
    wcel
    cA
    chsh
    cB
    chsh
    cA
    cB
    shub1
    syl2an
end
