include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "wss.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "wb.mm"
include "chsh.mm"
include "shlub.mm"
include "syl3an2.mm"
include "syl3an1.mm"

theorem chlub
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CH /\ B e. CH /\ C e. CH ) -> ( ( A C_ C /\ B C_ C ) <-> ( A vH B ) C_ C ) )

  proof
    cA
    cch
    wcel
    cA
    csh
    wcel
    #
    cB
    cch
    wcel
    #
    cC
    cch
    wcel
    #
    cA
    cC
    wss
    cB
    cC
    wss
    wa
    cA
    cB
    chj
    co
    cC
    wss
    wb
    #
    cA
    chsh
    @1
    @0
    cB
    csh
    wcel
    @2
    @3
    cB
    chsh
    cA
    cB
    cC
    shlub
    syl3an2
    syl3an1
end
