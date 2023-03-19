include "csca.mm"
include "c1.mm"
include "c8.mm"
include "cop.mm"
include "ipsstr.mm"
include "scaid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cvsca.mm"
include "cip.mm"
include "ctp.mm"
include "snsstp1.mm"
include "cbs.mm"
include "cplusg.mm"
include "cmulr.mm"
include "cun.mm"
include "ssun2.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "strfv.mm"

theorem ipssca
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cI: class I
  let cV: class V
  assume ipspart.a: |- A = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u. { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. , <. ( .i ` ndx ) , I >. } )


  assert |- ( S e. V -> S = ( Scalar ` A ) )

  proof
    cS
    cA
    csca
    cV
    c1
    c8
    cop
    cA
    cB
    c.pl
    cS
    c.x
    c.xp
    cI
    ipspart.a
    ipsstr
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
    cnx
    cip
    cfv
    cI
    cop
    #
    ctp
    #
    cA
    @0
    @1
    @2
    snsstp1
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
    c.xp
    cop
    ctp
    #
    @3
    cun
    cA
    @3
    @4
    ssun2
    ipspart.a
    sseqtr4i
    sstri
    strfv
end
