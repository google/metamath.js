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
include "cts.mm"
include "cple.mm"
include "cds.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "cstr.mm"
include "c8.mm"
include "c9.mm"
include "eqid.mm"
include "ipsstr.mm"
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
include "8lt9.mm"
include "strleun.mm"
include "eqbrtri.mm"

theorem imasvalstr
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let c.xi: class .,
  let cL: class L
  let cO: class O
  assume imasvalstr.u: |- U = ( ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u. { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. , <. ( .i ` ndx ) , ., >. } ) u. { <. ( TopSet ` ndx ) , O >. , <. ( le ` ndx ) , L >. , <. ( dist ` ndx ) , D >. } )


  assert |- U Struct <. 1 , ; 1 2 >.

  proof
    cU
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
    c.xi
    cop
    ctp
    cun
    #
    cnx
    cts
    cfv
    #
    cO
    cop
    cnx
    cple
    cfv
    #
    cL
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
    imasvalstr.u
    c1
    c8
    c9
    @5
    @0
    @4
    @0
    cB
    c.pl
    cS
    c.x
    c.xp
    c.xi
    @0
    eqid
    ipsstr
    @1
    @2
    @3
    c9
    c1
    cc0
    cdc
    @5
    cO
    cL
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
    8lt9
    strleun
    eqbrtri
end
