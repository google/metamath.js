include "csca.mm"
include "c1.mm"
include "c6.mm"
include "cop.mm"
include "algstr.mm"
include "scaid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cvsca.mm"
include "cpr.mm"
include "snsspr1.mm"
include "cbs.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "cun.mm"
include "ssun2.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "strfv.mm"

theorem algsca
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cV: class V
  assume algpart.a: |- A = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u. { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. } )


  assert |- ( S e. V -> S = ( Scalar ` A ) )

  proof
    cS
    cA
    csca
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
    scaid
    cnx
    csca
    cfv
    cS
    cop
    #
    csn
    @0
    cnx
    cvsca
    cfv
    c.x
    cop
    #
    cpr
    #
    cA
    @0
    @1
    snsspr1
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
