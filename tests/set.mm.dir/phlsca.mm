include "csca.mm"
include "c1.mm"
include "c8.mm"
include "cop.mm"
include "phlstr.mm"
include "scaid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cbs.mm"
include "cplusg.mm"
include "ctp.mm"
include "snsstp3.mm"
include "cvsca.mm"
include "cip.mm"
include "cpr.mm"
include "cun.mm"
include "ssun1.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "strfv.mm"

theorem phlsca
  let cB: class B
  let c.pl: class .+
  let cT: class T
  let c.x: class .x.
  let cH: class H
  let c.xi: class .,
  let cX: class X
  assume phlfn.h: |- H = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( Scalar ` ndx ) , T >. } u. { <. ( .s ` ndx ) , .x. >. , <. ( .i ` ndx ) , ., >. } )


  assert |- ( T e. X -> T = ( Scalar ` H ) )

  proof
    cT
    cH
    csca
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
    scaid
    cnx
    csca
    cfv
    cT
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
    cplusg
    cfv
    c.pl
    cop
    #
    @0
    ctp
    #
    cH
    @1
    @2
    @0
    snsstp3
    @3
    @3
    cnx
    cvsca
    cfv
    c.x
    cop
    cnx
    cip
    cfv
    c.xi
    cop
    cpr
    #
    cun
    cH
    @3
    @4
    ssun1
    phlfn.h
    sseqtr4i
    sstri
    strfv
end
