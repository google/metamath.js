include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "csca.mm"
include "cvsca.mm"
include "cip.mm"
include "cun.mm"
include "c1.mm"
include "c8.mm"
include "cstr.mm"
include "c3.mm"
include "c5.mm"
include "eqid.mm"
include "rngstr.mm"
include "c6.mm"
include "5nn.mm"
include "scandx.mm"
include "5lt6.mm"
include "6nn.mm"
include "vscandx.mm"
include "6lt8.mm"
include "8nn.mm"
include "ipndx.mm"
include "strle3.mm"
include "3lt5.mm"
include "strleun.mm"
include "eqbrtri.mm"

theorem ipsstr
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cI: class I
  assume ipspart.a: |- A = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u. { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. , <. ( .i ` ndx ) , I >. } )


  assert |- A Struct <. 1 , 8 >.

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
    cnx
    cip
    cfv
    #
    cI
    cop
    ctp
    #
    cun
    c1
    c8
    cop
    cstr
    ipspart.a
    c1
    c3
    c5
    c8
    @0
    @4
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
    c8
    cS
    c.x
    cI
    5nn
    scandx
    5lt6
    6nn
    vscandx
    6lt8
    8nn
    ipndx
    strle3
    3lt5
    strleun
    eqbrtri
end
