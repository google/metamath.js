include "c2.mm"
include "c6.mm"
include "cop.mm"
include "c3.mm"
include "c9.mm"
include "cpr.mm"
include "wceq.mm"
include "crn.mm"
include "rneq.mm"
include "csn.mm"
include "cun.mm"
include "df-pr.mm"
include "rneqi.mm"
include "rnun.mm"
include "cn.mm"
include "2nn.mm"
include "elexi.mm"
include "rnsnop.mm"
include "3nn.mm"
include "uneq12i.mm"
include "eqtr4i.mm"
include "3eqtri.mm"
include "syl6eq.mm"

theorem ex-rn
  let cF: class F


  assert |- ( F = { <. 2 , 6 >. , <. 3 , 9 >. } -> ran F = { 6 , 9 } )

  proof
    cF
    c2
    c6
    cop
    #
    c3
    c9
    cop
    #
    cpr
    #
    wceq
    cF
    crn
    @2
    crn
    #
    c6
    c9
    cpr
    #
    cF
    @2
    rneq
    @3
    @0
    csn
    #
    @1
    csn
    #
    cun
    #
    crn
    @5
    crn
    #
    @6
    crn
    #
    cun
    #
    @4
    @2
    @7
    @0
    @1
    df-pr
    rneqi
    @5
    @6
    rnun
    @10
    c6
    csn
    #
    c9
    csn
    #
    cun
    @4
    @8
    @11
    @9
    @12
    c2
    c6
    c2
    cn
    2nn
    elexi
    rnsnop
    c3
    c9
    c3
    cn
    3nn
    elexi
    rnsnop
    uneq12i
    c6
    c9
    df-pr
    eqtr4i
    3eqtri
    syl6eq
end
