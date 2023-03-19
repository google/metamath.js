include "cxp.mm"
include "wcel.mm"
include "cid.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "wceq.mm"
include "cvv.mm"
include "bj-elid.mm"
include "simprbi.mm"
include "wi.mm"
include "xpss.mm"
include "sseli.mm"
include "simplbi2.mm"
include "syl.mm"
include "impbid2.mm"

theorem bj-elid2
  let cA: class A
  let cV: class V
  let cW: class W


  assert |- ( A e. ( V X. W ) -> ( A e. _I <-> ( 1st ` A ) = ( 2nd ` A ) ) )

  proof
    cA
    cV
    cW
    cxp
    #
    wcel
    #
    cA
    cid
    wcel
    #
    cA
    c1st
    cfv
    cA
    c2nd
    cfv
    wceq
    #
    @2
    cA
    cvv
    cvv
    cxp
    #
    wcel
    #
    @3
    cA
    bj-elid
    #
    simprbi
    @1
    @5
    @3
    @2
    wi
    @0
    @4
    cA
    cV
    cW
    xpss
    sseli
    @2
    @5
    @3
    @6
    simplbi2
    syl
    impbid2
end
