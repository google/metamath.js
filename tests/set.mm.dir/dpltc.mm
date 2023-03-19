include "cdp2.mm"
include "cdp.mm"
include "co.mm"
include "clt.mm"
include "dp2ltc.mm"
include "dpval3rp.mm"
include "3brtr4i.mm"

theorem dpltc
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume dpltc.a: |- A e. NN0
  assume dpltc.b: |- B e. RR+
  assume dpltc.c: |- C e. NN0
  assume dpltc.d: |- D e. RR+
  assume dpltc.1: |- A < C
  assume dpltc.2: |- B < ; 1 0


  assert |- ( A . B ) < ( C . D )

  proof
    cA
    cB
    cdp2
    cC
    cD
    cdp2
    cA
    cB
    cdp
    co
    cC
    cD
    cdp
    co
    clt
    cA
    cB
    cC
    cD
    dpltc.a
    dpltc.b
    dpltc.c
    dpltc.d
    dpltc.2
    dpltc.1
    dp2ltc
    cA
    cB
    dpltc.a
    dpltc.b
    dpval3rp
    cC
    cD
    dpltc.c
    dpltc.d
    dpval3rp
    3brtr4i
end
