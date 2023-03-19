include "cbs.mm"
include "c1.mm"
include "c8.mm"
include "cop.mm"
include "phlstr.mm"
include "baseid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cplusg.mm"
include "csca.mm"
include "ctp.mm"
include "snsstp1.mm"
include "cvsca.mm"
include "cip.mm"
include "cpr.mm"
include "cun.mm"
include "ssun1.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "strfv.mm"

theorem phlbase
  let cB: class B
  let c.pl: class .+
  let cT: class T
  let c.x: class .x.
  let cH: class H
  let c.xi: class .,
  let cX: class X
  assume phlfn.h: |- H = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( Scalar ` ndx ) , T >. } u. { <. ( .s ` ndx ) , .x. >. , <. ( .i ` ndx ) , ., >. } )


  assert |- ( B e. X -> B = ( Base ` H ) )

  proof
    cB
    cH
    cbs
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
    cplusg
    cfv
    c.pl
    cop
    #
    cnx
    csca
    cfv
    cT
    cop
    #
    ctp
    #
    cH
    @0
    @1
    @2
    snsstp1
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
