include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "chsh.mm"
include "shlej2.mm"
include "syl3anl.mm"

theorem chlej2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. CH /\ B e. CH /\ C e. CH ) /\ A C_ B ) -> ( C vH A ) C_ ( C vH B ) )

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
    cC
    cA
    chj
    co
    cC
    cB
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
    shlej2
    syl3anl
end
