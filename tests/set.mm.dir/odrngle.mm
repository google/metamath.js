include "cple.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "cop.mm"
include "odrngstr.mm"
include "pleid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cts.mm"
include "cds.mm"
include "ctp.mm"
include "snsstp2.mm"
include "cbs.mm"
include "cplusg.mm"
include "cmulr.mm"
include "cun.mm"
include "ssun2.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "strfv.mm"

theorem odrngle
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let c.x: class .x.
  let cJ: class J
  let c.le: class .<_
  let cV: class V
  let cW: class W
  assume odrngstr.w: |- W = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .x. >. } u. { <. ( TopSet ` ndx ) , J >. , <. ( le ` ndx ) , .<_ >. , <. ( dist ` ndx ) , D >. } )


  assert |- ( .<_ e. V -> .<_ = ( le ` W ) )

  proof
    c.le
    cW
    cple
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
    pleid
    cnx
    cple
    cfv
    c.le
    cop
    #
    csn
    cnx
    cts
    cfv
    cJ
    cop
    #
    @0
    cnx
    cds
    cfv
    cD
    cop
    #
    ctp
    #
    cW
    @1
    @0
    @2
    snsstp2
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
