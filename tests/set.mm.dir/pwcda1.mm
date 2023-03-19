include "wcel.mm"
include "c1o.mm"
include "ccda.mm"
include "co.mm"
include "cpw.mm"
include "cxp.mm"
include "cen.mm"
include "con0.mm"
include "wbr.mm"
include "1on.mm"
include "pwcdaen.mm"
include "mpan2.mm"
include "c2o.mm"
include "c0.mm"
include "csn.mm"
include "cpr.mm"
include "pwpw0.mm"
include "df1o2.mm"
include "pweqi.mm"
include "df2o2.mm"
include "3eqtr4i.mm"
include "xpeq2i.mm"
include "cvv.mm"
include "wceq.mm"
include "pwexg.mm"
include "xp2cda.mm"
include "syl.mm"
include "syl5eq.mm"
include "breqtrd.mm"
include "ensymd.mm"

theorem pwcda1
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( ~P A +c ~P A ) ~~ ~P ( A +c 1o ) )

  proof
    cA
    cV
    wcel
    #
    cA
    c1o
    ccda
    co
    cpw
    #
    cA
    cpw
    #
    @2
    ccda
    co
    #
    @0
    @1
    @2
    c1o
    cpw
    #
    cxp
    #
    @3
    cen
    @0
    c1o
    con0
    wcel
    @1
    @5
    cen
    wbr
    1on
    cA
    c1o
    cV
    con0
    pwcdaen
    mpan2
    @0
    @5
    @2
    c2o
    cxp
    #
    @3
    @4
    c2o
    @2
    c0
    csn
    #
    cpw
    c0
    @7
    cpr
    @4
    c2o
    pwpw0
    c1o
    @7
    df1o2
    pweqi
    df2o2
    3eqtr4i
    xpeq2i
    @0
    @2
    cvv
    wcel
    @6
    @3
    wceq
    cA
    cV
    pwexg
    @2
    cvv
    xp2cda
    syl
    syl5eq
    breqtrd
    ensymd
end
