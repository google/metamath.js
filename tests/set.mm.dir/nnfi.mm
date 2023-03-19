include "com.mm"
include "cfn.mm"
include "con0.mm"
include "cin.mm"
include "onfin2.mm"
include "inss2.mm"
include "eqsstri.mm"
include "sseli.mm"

theorem nnfi
  let cA: class A


  assert |- ( A e. _om -> A e. Fin )

  proof
    com
    cfn
    cA
    com
    con0
    cfn
    cin
    cfn
    onfin2
    con0
    cfn
    inss2
    eqsstri
    sseli
end
