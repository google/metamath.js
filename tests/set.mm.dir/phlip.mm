include "cip.mm"
include "c1.mm"
include "c8.mm"
include "cop.mm"
include "phlstr.mm"
include "ipid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cvsca.mm"
include "cpr.mm"
include "snsspr2.mm"
include "cbs.mm"
include "cplusg.mm"
include "csca.mm"
include "ctp.mm"
include "cun.mm"
include "ssun2.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "strfv.mm"

theorem phlip
  let cB: class B
  let c.pl: class .+
  let cT: class T
  let c.x: class .x.
  let cH: class H
  let c.xi: class .,
  let cX: class X
  assume phlfn.h: |- H = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( Scalar ` ndx ) , T >. } u. { <. ( .s ` ndx ) , .x. >. , <. ( .i ` ndx ) , ., >. } )


  assert |- ( ., e. X -> ., = ( .i ` H ) )

  proof
    c.xi
    cH
    cip
    cX
    c1
    c8
    cop
    cB
    c.pl
    cT
    c.x
    cH
    c.xi
    phlfn.h
    phlstr
    ipid
    cnx
    cip
    cfv
    c.xi
    cop
    #
    csn
    cnx
    cvsca
    cfv
    c.x
    cop
    #
    @0
    cpr
    #
    cH
    @1
    @0
    snsspr2
    @2
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
    csca
    cfv
    cT
    cop
    ctp
    #
    @2
    cun
    cH
    @2
    @3
    ssun2
    phlfn.h
    sseqtr4i
    sstri
    strfv
end
