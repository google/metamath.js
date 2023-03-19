include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "chj.mm"
include "co.mm"
include "chsh.mm"
include "shjcl.mm"
include "syl2an.mm"

theorem chjcl
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A vH B ) e. CH )

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
    cch
    wcel
    cB
    cch
    wcel
    cA
    chsh
    cB
    chsh
    cA
    cB
    shjcl
    syl2an
end
