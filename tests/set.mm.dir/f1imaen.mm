include "wf1.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "cima.mm"
include "cen.mm"
include "wbr.mm"
include "f1imaeng.mm"
include "mp3an3.mm"

theorem f1imaen
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume f1imaen.1: |- C e. _V


  assert |- ( ( F : A -1-1-> B /\ C C_ A ) -> ( F " C ) ~~ C )

  proof
    cA
    cB
    cF
    wf1
    cC
    cA
    wss
    cC
    cvv
    wcel
    cF
    cC
    cima
    cC
    cen
    wbr
    f1imaen.1
    cA
    cB
    cC
    cF
    cvv
    f1imaeng
    mp3an3
end
