include "cbs.mm"
include "c1.mm"
include "c10.mm"
include "cop.mm"
include "otpsstrOLD.mm"
include "baseid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cts.mm"
include "cple.mm"
include "ctp.mm"
include "snsstp1.mm"
include "sseqtr4i.mm"
include "strfv.mm"

theorem otpsbasOLD
  let cB: class B
  let cJ: class J
  let cK: class K
  let c.le: class .<_
  let cV: class V
  assume otpsstr.w: |- K = { <. ( Base ` ndx ) , B >. , <. ( TopSet ` ndx ) , J >. , <. ( le ` ndx ) , .<_ >. }


  assert |- ( B e. V -> B = ( Base ` K ) )

  proof
    cB
    cK
    cbs
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
    baseid
    cnx
    cbs
    cfv
    cB
    cop
    #
    csn
    @0
    cnx
    cts
    cfv
    cJ
    cop
    #
    cnx
    cple
    cfv
    c.le
    cop
    #
    ctp
    cK
    @0
    @1
    @2
    snsstp1
    otpsstr.w
    sseqtr4i
    strfv
end
