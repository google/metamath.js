include "cplusg.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "cop.mm"
include "odrngstr.mm"
include "plusgid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cbs.mm"
include "cmulr.mm"
include "ctp.mm"
include "snsstp2.mm"
include "cts.mm"
include "cple.mm"
include "cds.mm"
include "cun.mm"
include "ssun1.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "strfv.mm"

theorem odrngplusg
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let c.x: class .x.
  let cJ: class J
  let c.le: class .<_
  let cV: class V
  let cW: class W
  assume odrngstr.w: |- W = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .x. >. } u. { <. ( TopSet ` ndx ) , J >. , <. ( le ` ndx ) , .<_ >. , <. ( dist ` ndx ) , D >. } )


  assert |- ( .+ e. V -> .+ = ( +g ` W ) )

  proof
    c.pl
    cW
    cplusg
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
    plusgid
    cnx
    cplusg
    cfv
    c.pl
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
    cmulr
    cfv
    c.x
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
    @3
    cnx
    cts
    cfv
    cJ
    cop
    cnx
    cple
    cfv
    c.le
    cop
    cnx
    cds
    cfv
    cD
    cop
    ctp
    #
    cun
    cW
    @3
    @4
    ssun1
    odrngstr.w
    sseqtr4i
    sstri
    strfv
end
