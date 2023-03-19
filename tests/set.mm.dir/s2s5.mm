include "cs1.mm"
include "cs2.mm"
include "cconcat.mm"
include "co.mm"
include "cs4.mm"
include "cs3.mm"
include "cs5.mm"
include "cs7.mm"
include "s1s2.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "s1cli.mm"
include "s4cli.mm"
include "df-s2.mm"
include "s1s4.mm"
include "cats2cat.mm"
include "s3s4.mm"
include "3eqtr4ri.mm"

theorem s2s5
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G


  assert |- <" A B C D E F G "> = ( <" A B "> ++ <" C D E F G "> )

  proof
    cA
    cs1
    #
    cB
    cC
    cs2
    cconcat
    co
    #
    cD
    cE
    cF
    cG
    cs4
    #
    cconcat
    co
    cA
    cB
    cC
    cs3
    #
    @2
    cconcat
    co
    cA
    cB
    cs2
    #
    cC
    cD
    cE
    cF
    cG
    cs5
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
    s1s2
    eqcomi
    oveq1i
    @4
    @0
    @5
    @2
    cB
    cC
    cA
    s1cli
    cD
    cE
    cF
    cG
    s4cli
    cA
    cB
    df-s2
    cC
    cD
    cE
    cF
    cG
    s1s4
    cats2cat
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    s3s4
    3eqtr4ri
end
