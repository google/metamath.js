include "cvv.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "ccom.mm"
include "mapco2g.mm"
include "mp3an1.mm"

theorem mapco2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assume mapco2.3: |- E e. _V


  assert |- ( ( A e. ( B ^m C ) /\ D : E --> C ) -> ( A o. D ) e. ( B ^m E ) )

  proof
    cE
    cvv
    wcel
    cA
    cB
    cC
    cmap
    co
    wcel
    cE
    cC
    cD
    wf
    cA
    cD
    ccom
    cB
    cE
    cmap
    co
    wcel
    mapco2.3
    cA
    cB
    cC
    cD
    cE
    mapco2g
    mp3an1
end
