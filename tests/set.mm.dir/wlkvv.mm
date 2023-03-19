include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cwlks.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "wlkn0.mm"
include "2ndnpr.mm"
include "necon1ai.mm"
include "syl.mm"

theorem wlkvv
  let cG: class G
  let cW: class W


  assert |- ( ( 1st ` W ) ( Walks ` G ) ( 2nd ` W ) -> W e. ( _V X. _V ) )

  proof
    cW
    c1st
    cfv
    #
    cW
    c2nd
    cfv
    #
    cG
    cwlks
    cfv
    wbr
    @1
    c0
    wne
    cW
    cvv
    cvv
    cxp
    wcel
    #
    @1
    @0
    cG
    wlkn0
    @2
    @1
    c0
    cW
    2ndnpr
    necon1ai
    syl
end
