include "cz.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cfzo.mm"
include "csn.mm"
include "fzval3.mm"
include "fzsn.mm"
include "eqtr3d.mm"

theorem fzosn
  let cA: class A


  assert |- ( A e. ZZ -> ( A ..^ ( A + 1 ) ) = { A } )

  proof
    cA
    cz
    wcel
    cA
    cA
    cfz
    co
    cA
    cA
    c1
    caddc
    co
    cfzo
    co
    cA
    csn
    cA
    cA
    fzval3
    cA
    fzsn
    eqtr3d
end
