include "cple.mm"
include "c1.mm"
include "c10.mm"
include "cop.mm"
include "otpsstrOLD.mm"
include "pleid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cbs.mm"
include "cts.mm"
include "ctp.mm"
include "snsstp3.mm"
include "sseqtr4i.mm"
include "strfv.mm"

theorem otpsleOLD
  let cB: class B
  let cJ: class J
  let cK: class K
  let c.le: class .<_
  let cV: class V
  assume otpsstr.w: |- K = { <. ( Base ` ndx ) , B >. , <. ( TopSet ` ndx ) , J >. , <. ( le ` ndx ) , .<_ >. }


  assert |- ( .<_ e. V -> .<_ = ( le ` K ) )

  proof
    c.le
    cK
    cple
    cV
    c1
    c10
    cop
    cB
    cJ
    cK
    c.le
    otpsstr.w
    otpsstrOLD
    pleid
    cnx
    cple
    cfv
    c.le
    cop
    #
    csn
    cnx
    cbs
    cfv
    cB
    cop
    #
    cnx
    cts
    cfv
    cJ
    cop
    #
    @0
    ctp
    cK
    @1
    @2
    @0
    snsstp3
    otpsstr.w
    sseqtr4i
    strfv
end
