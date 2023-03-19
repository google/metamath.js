include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "chj.mm"
include "co.mm"
include "cun.mm"
include "cort.mm"
include "cfv.mm"
include "wceq.mm"
include "chsh.mm"
include "shjval.mm"
include "syl2an.mm"

theorem chjval
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A vH B ) = ( _|_ ` ( _|_ ` ( A u. B ) ) ) )

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
    cA
    cB
    cun
    cort
    cfv
    cort
    cfv
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
    shjval
    syl2an
end
