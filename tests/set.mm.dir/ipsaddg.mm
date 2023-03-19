include "cplusg.mm"
include "c1.mm"
include "c8.mm"
include "cop.mm"
include "ipsstr.mm"
include "plusgid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cbs.mm"
include "cmulr.mm"
include "ctp.mm"
include "snsstp2.mm"
include "csca.mm"
include "cvsca.mm"
include "cip.mm"
include "cun.mm"
include "ssun1.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "strfv.mm"

theorem ipsaddg
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cI: class I
  let cV: class V
  assume ipspart.a: |- A = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u. { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. , <. ( .i ` ndx ) , I >. } )


  assert |- ( .+ e. V -> .+ = ( +g ` A ) )

  proof
    c.pl
    cA
    cplusg
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
    c.xp
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
    @3
    cnx
    csca
    cfv
    cS
    cop
    cnx
    cvsca
    cfv
    c.x
    cop
    cnx
    cip
    cfv
    cI
    cop
    ctp
    #
    cun
    cA
    @3
    @4
    ssun1
    ipspart.a
    sseqtr4i
    sstri
    strfv
end
