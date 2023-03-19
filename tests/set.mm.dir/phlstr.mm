include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cplusg.mm"
include "csca.mm"
include "ctp.mm"
include "cvsca.mm"
include "csn.mm"
include "cun.mm"
include "cip.mm"
include "c1.mm"
include "c8.mm"
include "cstr.mm"
include "cpr.mm"
include "df-pr.mm"
include "uneq2i.mm"
include "unass.mm"
include "3eqtr4i.mm"
include "c6.mm"
include "eqid.mm"
include "lmodstr.mm"
include "8nn.mm"
include "ipndx.mm"
include "strle1.mm"
include "6lt8.mm"
include "strleun.mm"
include "eqbrtri.mm"

theorem phlstr
  let cB: class B
  let c.pl: class .+
  let cT: class T
  let c.x: class .x.
  let cH: class H
  let c.xi: class .,
  assume phlfn.h: |- H = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( Scalar ` ndx ) , T >. } u. { <. ( .s ` ndx ) , .x. >. , <. ( .i ` ndx ) , ., >. } )


  assert |- H Struct <. 1 , 8 >.

  proof
    cH
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
    cnx
    cvsca
    cfv
    c.x
    cop
    #
    csn
    #
    cun
    #
    cnx
    cip
    cfv
    #
    c.xi
    cop
    #
    csn
    #
    cun
    #
    c1
    c8
    cop
    cstr
    @0
    @1
    @5
    cpr
    #
    cun
    @0
    @2
    @6
    cun
    #
    cun
    cH
    @7
    @8
    @9
    @0
    @1
    @5
    df-pr
    uneq2i
    phlfn.h
    @0
    @2
    @6
    unass
    3eqtr4i
    c1
    c6
    c8
    c8
    @3
    @6
    cB
    c.pl
    c.x
    cT
    @3
    @3
    eqid
    lmodstr
    @4
    c8
    c.xi
    8nn
    ipndx
    strle1
    6lt8
    strleun
    eqbrtri
end
