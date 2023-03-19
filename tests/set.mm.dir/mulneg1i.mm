include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mulneg1.mm"
include "mp2an.mm"

theorem mulneg1i
  let cA: class A
  let cB: class B
  assume mulm1.1: |- A e. CC
  assume mulneg.2: |- B e. CC


  assert |- ( -u A x. B ) = -u ( A x. B )

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
    cmul
    co
    cA
    cB
    cmul
    co
    cneg
    wceq
    mulm1.1
    mulneg.2
    cA
    cB
    mulneg1
    mp2an
end
