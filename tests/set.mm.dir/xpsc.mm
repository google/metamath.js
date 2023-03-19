include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "c0.mm"
include "cxp.mm"
include "c1o.mm"
include "cun.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "snex.mm"
include "cdaval.mm"
include "mp2an.mm"
include "cnveqi.mm"
include "cnvun.mm"
include "cnvxp.mm"
include "uneq12i.mm"
include "3eqtri.mm"

theorem xpsc
  let cA: class A
  let cB: class B


  assert |- `' ( { A } +c { B } ) = ( ( { (/) } X. { A } ) u. ( { 1o } X. { B } ) )

  proof
    cA
    csn
    #
    cB
    csn
    #
    ccda
    co
    #
    ccnv
    @0
    c0
    csn
    #
    cxp
    #
    @1
    c1o
    csn
    #
    cxp
    #
    cun
    #
    ccnv
    @4
    ccnv
    #
    @6
    ccnv
    #
    cun
    @3
    @0
    cxp
    #
    @5
    @1
    cxp
    #
    cun
    @2
    @7
    @0
    cvv
    wcel
    @1
    cvv
    wcel
    @2
    @7
    wceq
    cA
    snex
    cB
    snex
    @0
    @1
    cvv
    cvv
    cdaval
    mp2an
    cnveqi
    @4
    @6
    cnvun
    @8
    @10
    @9
    @11
    @0
    @3
    cnvxp
    @1
    @5
    cnvxp
    uneq12i
    3eqtri
end
