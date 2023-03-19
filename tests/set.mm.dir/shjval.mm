include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "cun.mm"
include "cort.mm"
include "cfv.mm"
include "wceq.mm"
include "shss.mm"
include "sshjval.mm"
include "syl2an.mm"

theorem shjval
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. SH /\ B e. SH ) -> ( A vH B ) = ( _|_ ` ( _|_ ` ( A u. B ) ) ) )

  proof
    cA
    csh
    wcel
    cA
    chil
    wss
    cB
    chil
    wss
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
    csh
    wcel
    cA
    shss
    cB
    shss
    cA
    cB
    sshjval
    syl2an
end
