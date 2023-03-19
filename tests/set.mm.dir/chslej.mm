include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "cph.mm"
include "co.mm"
include "chj.mm"
include "wss.mm"
include "chsh.mm"
include "shslej.mm"
include "syl2an.mm"

theorem chslej
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A +H B ) C_ ( A vH B ) )

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
    cph
    co
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
    shslej
    syl2an
end
