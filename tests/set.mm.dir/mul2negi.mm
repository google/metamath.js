include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mul2neg.mm"
include "mp2an.mm"

theorem mul2negi
  let cA: class A
  let cB: class B
  assume mulm1.1: |- A e. CC
  assume mulneg.2: |- B e. CC


  assert |- ( -u A x. -u B ) = ( A x. B )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cneg
    cB
    cneg
    cmul
    co
    cA
    cB
    cmul
    co
    wceq
    mulm1.1
    mulneg.2
    cA
    cB
    mul2neg
    mp2an
end
