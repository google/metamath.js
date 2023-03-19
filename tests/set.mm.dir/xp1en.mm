include "wcel.mm"
include "c1o.mm"
include "cxp.mm"
include "c0.mm"
include "csn.mm"
include "cen.mm"
include "df1o2.mm"
include "xpeq2i.mm"
include "cvv.mm"
include "wbr.mm"
include "0ex.mm"
include "xpsneng.mm"
include "mpan2.mm"
include "syl5eqbr.mm"

theorem xp1en
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( A X. 1o ) ~~ A )

  proof
    cA
    cV
    wcel
    #
    cA
    c1o
    cxp
    cA
    c0
    csn
    #
    cxp
    #
    cA
    cen
    c1o
    @1
    cA
    df1o2
    xpeq2i
    @0
    c0
    cvv
    wcel
    @2
    cA
    cen
    wbr
    0ex
    cA
    c0
    cV
    cvv
    xpsneng
    mpan2
    syl5eqbr
end
