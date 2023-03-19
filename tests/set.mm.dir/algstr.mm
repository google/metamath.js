include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "csca.mm"
include "cvsca.mm"
include "cpr.mm"
include "cun.mm"
include "c1.mm"
include "c6.mm"
include "cstr.mm"
include "c3.mm"
include "c5.mm"
include "eqid.mm"
include "rngstr.mm"
include "5nn.mm"
include "scandx.mm"
include "5lt6.mm"
include "6nn.mm"
include "vscandx.mm"
include "strle2.mm"
include "3lt5.mm"
include "strleun.mm"
include "eqbrtri.mm"

theorem algstr
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  assume algpart.a: |- A = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u. { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. } )


  assert |- A Struct <. 1 , 6 >.

  proof
    cA
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
    cS
    cop
    cnx
    cvsca
    cfv
    #
    c.x
    cop
    cpr
    #
    cun
    c1
    c6
    cop
    cstr
    algpart.a
    c1
    c3
    c5
    c6
    @0
    @3
    cB
    c.pl
    @0
    c.xp
    @0
    eqid
    rngstr
    @1
    @2
    c5
    c6
    cS
    c.x
    5nn
    scandx
    5lt6
    6nn
    vscandx
    strle2
    3lt5
    strleun
    eqbrtri
end
