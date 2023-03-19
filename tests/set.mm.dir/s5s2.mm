include "cs4.mm"
include "cs2.mm"
include "cconcat.mm"
include "co.mm"
include "cs1.mm"
include "cs6.mm"
include "cs5.mm"
include "cs7.mm"
include "s4s2.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "s4cli.mm"
include "s1cli.mm"
include "df-s5.mm"
include "df-s2.mm"
include "cats2cat.mm"
include "df-s7.mm"
include "3eqtr4ri.mm"

theorem s5s2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G


  assert |- <" A B C D E F G "> = ( <" A B C D E "> ++ <" F G "> )

  proof
    cA
    cB
    cC
    cD
    cs4
    #
    cE
    cF
    cs2
    cconcat
    co
    #
    cG
    cs1
    #
    cconcat
    co
    cA
    cB
    cC
    cD
    cE
    cF
    cs6
    #
    @2
    cconcat
    co
    cA
    cB
    cC
    cD
    cE
    cs5
    #
    cF
    cG
    cs2
    #
    cconcat
    co
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    cs7
    @1
    @3
    @2
    cconcat
    @3
    @1
    cA
    cB
    cC
    cD
    cE
    cF
    s4s2
    eqcomi
    oveq1i
    @4
    @0
    @5
    @2
    cE
    cF
    cA
    cB
    cC
    cD
    s4cli
    cG
    s1cli
    cA
    cB
    cC
    cD
    cE
    df-s5
    cF
    cG
    df-s2
    cats2cat
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    df-s7
    3eqtr4ri
end
