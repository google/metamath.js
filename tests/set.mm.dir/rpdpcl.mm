include "cdp.mm"
include "co.mm"
include "cdp2.mm"
include "crp.mm"
include "dpval3rp.mm"
include "rpdp2cl.mm"
include "eqeltri.mm"

theorem rpdpcl
  let cA: class A
  let cB: class B
  assume rpdpcl.a: |- A e. NN0
  assume rpdpcl.b: |- B e. RR+


  assert |- ( A . B ) e. RR+

  proof
    cA
    cB
    cdp
    co
    cA
    cB
    cdp2
    crp
    cA
    cB
    rpdpcl.a
    rpdpcl.b
    dpval3rp
    cA
    cB
    rpdpcl.a
    rpdpcl.b
    rpdp2cl
    eqeltri
end
