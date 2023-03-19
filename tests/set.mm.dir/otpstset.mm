include "cts.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cop.mm"
include "otpsstr.mm"
include "tsetid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cbs.mm"
include "cple.mm"
include "ctp.mm"
include "snsstp2.mm"
include "sseqtr4i.mm"
include "strfv.mm"

theorem otpstset
  let cB: class B
  let cJ: class J
  let cK: class K
  let c.le: class .<_
  let cV: class V
  assume otpsstr.w: |- K = { <. ( Base ` ndx ) , B >. , <. ( TopSet ` ndx ) , J >. , <. ( le ` ndx ) , .<_ >. }


  assert |- ( J e. V -> J = ( TopSet ` K ) )

  proof
    cJ
    cK
    cts
    cV
    c1
    c1
    cc0
    cdc
    cop
    cB
    cJ
    cK
    c.le
    otpsstr.w
    otpsstr
    tsetid
    cnx
    cts
    cfv
    cJ
    cop
    #
    csn
    cnx
    cbs
    cfv
    cB
    cop
    #
    @0
    cnx
    cple
    cfv
    c.le
    cop
    #
    ctp
    cK
    @1
    @0
    @2
    snsstp2
    otpsstr.w
    sseqtr4i
    strfv
end
