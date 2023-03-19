include "cwlks.mm"
include "cfv.mm"
include "wcel.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "wceq.mm"
include "wbr.mm"
include "wlkop.mm"
include "cvv.mm"
include "cxp.mm"
include "wlkvv.mm"
include "1st2ndb.mm"
include "sylib.mm"
include "eleq1.mm"
include "df-br.mm"
include "syl6bbr.mm"
include "pm5.21nii.mm"

theorem wlkcpr
  let cG: class G
  let cW: class W


  assert |- ( W e. ( Walks ` G ) <-> ( 1st ` W ) ( Walks ` G ) ( 2nd ` W ) )

  proof
    cW
    cG
    cwlks
    cfv
    #
    wcel
    #
    cW
    cW
    c1st
    cfv
    #
    cW
    c2nd
    cfv
    #
    cop
    #
    wceq
    #
    @2
    @3
    @0
    wbr
    #
    cG
    cW
    wlkop
    @6
    cW
    cvv
    cvv
    cxp
    wcel
    @5
    cG
    cW
    wlkvv
    cW
    1st2ndb
    sylib
    @5
    @1
    @4
    @0
    wcel
    @6
    cW
    @4
    @0
    eleq1
    @2
    @3
    @0
    df-br
    syl6bbr
    pm5.21nii
end
