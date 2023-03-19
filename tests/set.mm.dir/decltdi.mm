include "le9lt10.mm"
include "declti.mm"

theorem decltdi
  let cA: class A
  let cB: class B
  let cC: class C
  assume declti.a: |- A e. NN
  assume declti.b: |- B e. NN0
  assume declti.c: |- C e. NN0
  assume decltdi.4: |- C <_ 9


  assert |- C < ; A B

  proof
    cA
    cB
    cC
    declti.a
    declti.b
    declti.c
    cC
    declti.c
    decltdi.4
    le9lt10
    declti
end
