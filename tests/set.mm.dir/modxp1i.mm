include "c1.mm"
include "1nn0.mm"
include "nnnn0i.mm"
include "cexp.mm"
include "co.mm"
include "cmo.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "nncni.mm"
include "exp1.mm"
include "ax-mp.mm"
include "oveq1i.mm"
include "modxai.mm"

theorem modxp1i
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
  assume modxp1i.9: |- ( ( A ^ B ) mod N ) = ( K mod N )
  assume modxp1i.7: |- ( B + 1 ) = E
  assume modxp1i.8: |- ( ( D x. N ) + M ) = ( K x. A )


  assert |- ( ( A ^ E ) mod N ) = ( M mod N )

  proof
    cA
    cB
    c1
    cD
    cE
    cK
    cA
    cM
    cN
    modxai.1
    modxai.2
    modxai.3
    modxai.4
    modxai.5
    modxai.6
    1nn0
    cA
    modxai.2
    nnnn0i
    modxp1i.9
    cA
    c1
    cexp
    co
    #
    cA
    cN
    cmo
    cA
    cc
    wcel
    @0
    cA
    wceq
    cA
    modxai.2
    nncni
    cA
    exp1
    ax-mp
    oveq1i
    modxp1i.7
    modxp1i.8
    modxai
end
