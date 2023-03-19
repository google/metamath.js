include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cop.mm"
include "cpr.mm"
include "wfun.mm"
include "pm3.2i.mm"
include "funprg.mm"
include "mp3an12.mm"

theorem funpr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume funpr.1: |- A e. _V
  assume funpr.2: |- B e. _V
  assume funpr.3: |- C e. _V
  assume funpr.4: |- D e. _V


  assert |- ( A =/= B -> Fun { <. A , C >. , <. B , D >. } )

  proof
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    cC
    cvv
    wcel
    #
    cD
    cvv
    wcel
    #
    wa
    cA
    cB
    wne
    cA
    cC
    cop
    cB
    cD
    cop
    cpr
    wfun
    @0
    @1
    funpr.1
    funpr.2
    pm3.2i
    @2
    @3
    funpr.3
    funpr.4
    pm3.2i
    cA
    cB
    cC
    cD
    cvv
    cvv
    cvv
    cvv
    funprg
    mp3an12
end
