include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "subdi.mm"
include "mp3an.mm"

theorem subdii
  let cA: class A
  let cB: class B
  let cC: class C
  assume mulm1.1: |- A e. CC
  assume mulneg.2: |- B e. CC
  assume subdi.3: |- C e. CC


  assert |- ( A x. ( B - C ) ) = ( ( A x. B ) - ( A x. C ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    cc
    wcel
    cA
    cB
    cC
    cmin
    co
    cmul
    co
    cA
    cB
    cmul
    co
    cA
    cC
    cmul
    co
    cmin
    co
    wceq
    mulm1.1
    mulneg.2
    subdi.3
    cA
    cB
    cC
    subdi
    mp3an
end
