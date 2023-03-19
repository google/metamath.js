include "cs2.mm"
include "cconcat.mm"
include "co.mm"
include "cs3.mm"
include "cs4.mm"
include "cs7.mm"
include "s2s2.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "s2cli.mm"
include "s3cli.mm"
include "df-s3.mm"
include "s1s3.mm"
include "cats2cat.mm"
include "s4s3.mm"
include "3eqtr4ri.mm"

theorem s3s4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G


  assert |- <" A B C D E F G "> = ( <" A B C "> ++ <" D E F G "> )

  proof
    cA
    cB
    cs2
    #
    cC
    cD
    cs2
    cconcat
    co
    #
    cE
    cF
    cG
    cs3
    #
    cconcat
    co
    cA
    cB
    cC
    cD
    cs4
    #
    @2
    cconcat
    co
    cA
    cB
    cC
    cs3
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
    s2s2
    eqcomi
    oveq1i
    @4
    @0
    @5
    @2
    cC
    cD
    cA
    cB
    s2cli
    cE
    cF
    cG
    s3cli
    cA
    cB
    cC
    df-s3
    cD
    cE
    cF
    cG
    s1s3
    cats2cat
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    s4s3
    3eqtr4ri
end
