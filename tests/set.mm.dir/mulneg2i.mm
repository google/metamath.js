include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mulneg2.mm"
include "mp2an.mm"

theorem mulneg2i
  let cA: class A
  let cB: class B
  assume mulm1.1: |- A e. CC
  assume mulneg.2: |- B e. CC


  assert |- ( A x. -u B ) = -u ( A x. B )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    cneg
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
    mulneg2
    mp2an
end
