include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "cch.mm"
include "shss.mm"
include "sshjcl.mm"
include "syl2an.mm"

theorem shjcl
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. SH /\ B e. SH ) -> ( A vH B ) e. CH )

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
    cch
    wcel
    cB
    csh
    wcel
    cA
    shss
    cB
    shss
    cA
    cB
    sshjcl
    syl2an
end
