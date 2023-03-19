include "cch.mm"
include "wcel.mm"
include "chj.mm"
include "co.mm"
include "cun.mm"
include "cort.mm"
include "cfv.mm"
include "wceq.mm"
include "chjval.mm"
include "mp2an.mm"

theorem chjvali
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D
  assume chjval.1: |- A e. CH
  assume chjval.2: |- B e. CH


  assert |- ( A vH B ) = ( _|_ ` ( _|_ ` ( A u. B ) ) )

  proof
    cA
    cch
    wcel
    cB
    cch
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
    chjval.1
    chjval.2
    cA
    cB
    chjval
    mp2an
end
