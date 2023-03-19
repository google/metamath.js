include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "clt.mm"
include "nnnn0i.mm"
include "num0h.mm"
include "0nn0.mm"
include "nngt0i.mm"
include "numltc.mm"
include "eqbrtri.mm"

theorem numlti
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  assume numlti.1: |- T e. NN
  assume numlti.2: |- A e. NN
  assume numlti.3: |- B e. NN0
  assume numlti.4: |- C e. NN0
  assume numlti.5: |- C < T


  assert |- C < ( ( T x. A ) + B )

  proof
    cC
    cT
    cc0
    cmul
    co
    cC
    caddc
    co
    cT
    cA
    cmul
    co
    cB
    caddc
    co
    clt
    cC
    cT
    cT
    numlti.1
    nnnn0i
    numlti.4
    num0h
    cc0
    cA
    cC
    cB
    cT
    numlti.1
    0nn0
    cA
    numlti.2
    nnnn0i
    numlti.4
    numlti.3
    numlti.5
    cA
    numlti.2
    nngt0i
    numltc
    eqbrtri
end
