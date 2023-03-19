include "cds.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "cop.mm"
include "odrngstr.mm"
include "dsid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cts.mm"
include "cple.mm"
include "ctp.mm"
include "snsstp3.mm"
include "cbs.mm"
include "cplusg.mm"
include "cmulr.mm"
include "cun.mm"
include "ssun2.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "strfv.mm"

theorem odrngds
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let c.x: class .x.
  let cJ: class J
  let c.le: class .<_
  let cV: class V
  let cW: class W
  assume odrngstr.w: |- W = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .x. >. } u. { <. ( TopSet ` ndx ) , J >. , <. ( le ` ndx ) , .<_ >. , <. ( dist ` ndx ) , D >. } )


  assert |- ( D e. V -> D = ( dist ` W ) )

  proof
    cD
    cW
    cds
    cV
    c1
    c1
    c2
    cdc
    cop
    cB
    cD
    c.pl
    c.x
    cJ
    c.le
    cW
    odrngstr.w
    odrngstr
    dsid
    cnx
    cds
    cfv
    cD
    cop
    #
    csn
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
    @0
    ctp
    #
    cW
    @1
    @2
    @0
    snsstp3
    @3
    cnx
    cbs
    cfv
    cB
    cop
    cnx
    cplusg
    cfv
    c.pl
    cop
    cnx
    cmulr
    cfv
    c.x
    cop
    ctp
    #
    @3
    cun
    cW
    @3
    @4
    ssun2
    odrngstr.w
    sseqtr4i
    sstri
    strfv
end
