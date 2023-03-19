include "cop.mm"
include "cxp.mm"
include "wcel.mm"
include "opelxp1.mm"
include "syl.mm"

theorem otelxp1
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T


  assert |- ( <. <. A , B >. , C >. e. ( ( R X. S ) X. T ) -> A e. R )

  proof
    cA
    cB
    cop
    #
    cC
    cop
    cR
    cS
    cxp
    #
    cT
    cxp
    wcel
    @0
    @1
    wcel
    cA
    cR
    wcel
    @0
    cC
    @1
    cT
    opelxp1
    cA
    cB
    cR
    cS
    opelxp1
    syl
end
