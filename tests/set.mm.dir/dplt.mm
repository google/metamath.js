include "cdp2.mm"
include "cdp.mm"
include "co.mm"
include "clt.mm"
include "dp2lt.mm"
include "dpval3rp.mm"
include "3brtr4i.mm"

theorem dplt
  let cA: class A
  let cB: class B
  let cC: class C
  assume dplt.a: |- A e. NN0
  assume dplt.b: |- B e. RR+
  assume dplt.d: |- C e. RR+
  assume dplt.1: |- B < C


  assert |- ( A . B ) < ( A . C )

  proof
    cA
    cB
    cdp2
    cA
    cC
    cdp2
    cA
    cB
    cdp
    co
    cA
    cC
    cdp
    co
    clt
    cA
    cB
    cC
    dplt.a
    dplt.b
    dplt.d
    dplt.1
    dp2lt
    cA
    cB
    dplt.a
    dplt.b
    dpval3rp
    cA
    cC
    dplt.a
    dplt.d
    dpval3rp
    3brtr4i
end
