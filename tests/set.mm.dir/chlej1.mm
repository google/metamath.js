include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "chsh.mm"
include "shlej1.mm"
include "syl3anl.mm"

theorem chlej1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. CH /\ B e. CH /\ C e. CH ) /\ A C_ B ) -> ( A vH C ) C_ ( B vH C ) )

  proof
    cA
    cch
    wcel
    cA
    csh
    wcel
    cB
    cch
    wcel
    cB
    csh
    wcel
    cC
    cch
    wcel
    cC
    csh
    wcel
    cA
    cB
    wss
    cA
    cC
    chj
    co
    cB
    cC
    chj
    co
    wss
    cA
    chsh
    cB
    chsh
    cC
    chsh
    cA
    cB
    cC
    shlej1
    syl3anl
end
