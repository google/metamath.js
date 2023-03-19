include "c1.mm"
include "c3.mm"
include "c5.mm"
include "c9.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "csca.mm"
include "cvsca.mm"
include "cts.mm"
include "eqid.mm"
include "rngstr.mm"
include "c6.mm"
include "5nn.mm"
include "scandx.mm"
include "5lt6.mm"
include "6nn.mm"
include "vscandx.mm"
include "6lt9.mm"
include "9nn.mm"
include "tsetndx.mm"
include "strle3.mm"
include "3lt5.mm"
include "strleun.mm"

theorem psrvalstr
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cJ: class J


  assert |- ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u. { <. ( Scalar ` ndx ) , R >. , <. ( .s ` ndx ) , .x. >. , <. ( TopSet ` ndx ) , J >. } ) Struct <. 1 , 9 >.

  proof
    c1
    c3
    c5
    c9
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
    cnx
    csca
    cfv
    #
    cR
    cop
    cnx
    cvsca
    cfv
    #
    c.x
    cop
    cnx
    cts
    cfv
    #
    cJ
    cop
    ctp
    cB
    c.pl
    @0
    c.xp
    @0
    eqid
    rngstr
    @1
    @2
    @3
    c5
    c6
    c9
    cR
    c.x
    cJ
    5nn
    scandx
    5lt6
    6nn
    vscandx
    6lt9
    9nn
    tsetndx
    strle3
    3lt5
    strleun
end
