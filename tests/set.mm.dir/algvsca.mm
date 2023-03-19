include "cvsca.mm"
include "c1.mm"
include "c6.mm"
include "cop.mm"
include "algstr.mm"
include "vscaid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "csca.mm"
include "cpr.mm"
include "snsspr2.mm"
include "cbs.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "cun.mm"
include "ssun2.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "strfv.mm"

theorem algvsca
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cV: class V
  assume algpart.a: |- A = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u. { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. } )


  assert |- ( .x. e. V -> .x. = ( .s ` A ) )

  proof
    c.x
    cA
    cvsca
    cV
    c1
    c6
    cop
    cA
    cB
    c.pl
    cS
    c.x
    c.xp
    algpart.a
    algstr
    vscaid
    cnx
    cvsca
    cfv
    c.x
    cop
    #
    csn
    cnx
    csca
    cfv
    cS
    cop
    #
    @0
    cpr
    #
    cA
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
    cmulr
    cfv
    c.xp
    cop
    ctp
    #
    @2
    cun
    cA
    @2
    @3
    ssun2
    algpart.a
    sseqtr4i
    sstri
    strfv
end
