include "c2.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "nn0cni.mm"
include "2timesi.mm"
include "eqtr3i.mm"
include "modxai.mm"

theorem mod2xi
  let cA: class A
  let cB: class B
  let cD: class D
  let cE: class E
  let cK: class K
  let cM: class M
  let cN: class N
  assume modxai.1: |- N e. NN
  assume modxai.2: |- A e. NN
  assume modxai.3: |- B e. NN0
  assume modxai.4: |- D e. ZZ
  assume modxai.5: |- K e. NN0
  assume modxai.6: |- M e. NN0
  assume mod2xi.9: |- ( ( A ^ B ) mod N ) = ( K mod N )
  assume mod2xi.7: |- ( 2 x. B ) = E
  assume mod2xi.8: |- ( ( D x. N ) + M ) = ( K x. K )


  assert |- ( ( A ^ E ) mod N ) = ( M mod N )

  proof
    cA
    cB
    cB
    cD
    cE
    cK
    cK
    cM
    cN
    modxai.1
    modxai.2
    modxai.3
    modxai.4
    modxai.5
    modxai.6
    modxai.3
    modxai.5
    mod2xi.9
    mod2xi.9
    c2
    cB
    cmul
    co
    cB
    cB
    caddc
    co
    cE
    cB
    cB
    modxai.3
    nn0cni
    2timesi
    mod2xi.7
    eqtr3i
    mod2xi.8
    modxai
end
