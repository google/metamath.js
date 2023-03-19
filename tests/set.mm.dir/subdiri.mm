include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "subdir.mm"
include "mp3an.mm"

theorem subdiri
  let cA: class A
  let cB: class B
  let cC: class C
  assume mulm1.1: |- A e. CC
  assume mulneg.2: |- B e. CC
  assume subdi.3: |- C e. CC


  assert |- ( ( A - B ) x. C ) = ( ( A x. C ) - ( B x. C ) )

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
    cmin
    co
    cC
    cmul
    co
    cA
    cC
    cmul
    co
    cB
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
    subdir
    mp3an
end
