include "wcel.mm"
include "ccda.mm"
include "co.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "c1o.mm"
include "cun.mm"
include "c2o.mm"
include "wceq.mm"
include "cdaval.mm"
include "anidms.mm"
include "cpr.mm"
include "df2o3.mm"
include "df-pr.mm"
include "eqtri.mm"
include "xpeq2i.mm"
include "xpundi.mm"
include "syl6reqr.mm"

theorem xp2cda
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( A X. 2o ) = ( A +c A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cA
    ccda
    co
    #
    cA
    c0
    csn
    #
    cxp
    cA
    c1o
    csn
    #
    cxp
    cun
    #
    cA
    c2o
    cxp
    #
    @0
    @1
    @4
    wceq
    cA
    cA
    cV
    cV
    cdaval
    anidms
    @5
    cA
    @2
    @3
    cun
    #
    cxp
    @4
    c2o
    @6
    cA
    c2o
    c0
    c1o
    cpr
    @6
    df2o3
    c0
    c1o
    df-pr
    eqtri
    xpeq2i
    cA
    @2
    @3
    xpundi
    eqtri
    syl6reqr
end
