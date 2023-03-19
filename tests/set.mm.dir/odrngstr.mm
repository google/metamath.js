include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "cts.mm"
include "cple.mm"
include "cds.mm"
include "cun.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "cstr.mm"
include "c3.mm"
include "c9.mm"
include "eqid.mm"
include "rngstr.mm"
include "cc0.mm"
include "9nn.mm"
include "tsetndx.mm"
include "9lt10.mm"
include "10nn.mm"
include "plendx.mm"
include "1nn0.mm"
include "0nn0.mm"
include "2nn.mm"
include "2pos.mm"
include "declt.mm"
include "decnncl.mm"
include "dsndx.mm"
include "strle3.mm"
include "3lt9.mm"
include "strleun.mm"
include "eqbrtri.mm"

theorem odrngstr
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let c.x: class .x.
  let cJ: class J
  let c.le: class .<_
  let cW: class W
  assume odrngstr.w: |- W = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .x. >. } u. { <. ( TopSet ` ndx ) , J >. , <. ( le ` ndx ) , .<_ >. , <. ( dist ` ndx ) , D >. } )


  assert |- W Struct <. 1 , ; 1 2 >.

  proof
    cW
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
    c.x
    cop
    ctp
    #
    cnx
    cts
    cfv
    #
    cJ
    cop
    cnx
    cple
    cfv
    #
    c.le
    cop
    cnx
    cds
    cfv
    #
    cD
    cop
    ctp
    #
    cun
    c1
    c1
    c2
    cdc
    #
    cop
    cstr
    odrngstr.w
    c1
    c3
    c9
    @5
    @0
    @4
    cB
    c.pl
    @0
    c.x
    @0
    eqid
    rngstr
    @1
    @2
    @3
    c9
    c1
    cc0
    cdc
    @5
    cJ
    c.le
    cD
    9nn
    tsetndx
    9lt10
    10nn
    plendx
    c1
    cc0
    c2
    1nn0
    0nn0
    2nn
    2pos
    declt
    c1
    c2
    1nn0
    2nn
    decnncl
    dsndx
    strle3
    3lt9
    strleun
    eqbrtri
end
