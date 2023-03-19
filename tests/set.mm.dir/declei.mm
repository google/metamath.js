include "cc0.mm"
include "cdc.mm"
include "cle.mm"
include "dec0h.mm"
include "0nn0.mm"
include "nnnn0i.mm"
include "nngt0i.mm"
include "decleh.mm"
include "eqbrtri.mm"

theorem declei
  let cA: class A
  let cB: class B
  let cC: class C
  assume declei.1: |- A e. NN
  assume declei.2: |- B e. NN0
  assume declei.3: |- C e. NN0
  assume declei.4: |- C <_ 9


  assert |- C <_ ; A B

  proof
    cC
    cc0
    cC
    cdc
    cA
    cB
    cdc
    cle
    cC
    declei.3
    dec0h
    cc0
    cA
    cC
    cB
    0nn0
    cA
    declei.1
    nnnn0i
    declei.3
    declei.2
    declei.4
    cA
    declei.1
    nngt0i
    decleh
    eqbrtri
end
