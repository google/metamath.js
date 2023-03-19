include "cvsca.mm"
include "c1.mm"
include "c8.mm"
include "cop.mm"
include "ipsstr.mm"
include "vscaid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "csca.mm"
include "cip.mm"
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

theorem ipsvsca
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cI: class I
  let cV: class V
  assume ipspart.a: |- A = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u. { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. , <. ( .i ` ndx ) , I >. } )


  assert |- ( .x. e. V -> .x. = ( .s ` A ) )

  proof
    c.x
    cA
    cvsca
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
    cnx
    cip
    cfv
    cI
    cop
    #
    ctp
    #
    cA
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
