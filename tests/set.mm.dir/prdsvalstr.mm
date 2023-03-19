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
include "chom.mm"
include "cco.mm"
include "cpr.mm"
include "c1.mm"
include "c5.mm"
include "cdc.mm"
include "cstr.mm"
include "unass.mm"
include "c2.mm"
include "c4.mm"
include "eqid.mm"
include "imasvalstr.mm"
include "1nn0.mm"
include "4nn.mm"
include "decnncl.mm"
include "homndx.mm"
include "4nn0.mm"
include "5nn.mm"
include "4lt5.mm"
include "declt.mm"
include "ccondx.mm"
include "strle2.mm"
include "2nn0.mm"
include "2lt4.mm"
include "strleun.mm"
include "eqbrtrri.mm"

theorem prdsvalstr
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let c.xp: class .X.
  let cH: class H
  let c.xi: class .,
  let cL: class L
  let cO: class O


  assert |- ( ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u. { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. , <. ( .i ` ndx ) , ., >. } ) u. ( { <. ( TopSet ` ndx ) , O >. , <. ( le ` ndx ) , L >. , <. ( dist ` ndx ) , D >. } u. { <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .xb >. } ) ) Struct <. 1 , ; 1 5 >.

  proof
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
    cO
    cop
    cnx
    cple
    cfv
    cL
    cop
    cnx
    cds
    cfv
    cD
    cop
    ctp
    #
    cun
    #
    cnx
    chom
    cfv
    #
    cH
    cop
    cnx
    cco
    cfv
    #
    c.xb
    cop
    cpr
    #
    cun
    @0
    @1
    @5
    cun
    cun
    c1
    c1
    c5
    cdc
    #
    cop
    cstr
    @0
    @1
    @5
    unass
    c1
    c1
    c2
    cdc
    c1
    c4
    cdc
    #
    @6
    @2
    @5
    cB
    cD
    c.pl
    cS
    c.x
    c.xp
    @2
    c.xi
    cL
    cO
    @2
    eqid
    imasvalstr
    @3
    @4
    @7
    @6
    cH
    c.xb
    c1
    c4
    1nn0
    4nn
    decnncl
    homndx
    c1
    c4
    c5
    1nn0
    4nn0
    5nn
    4lt5
    declt
    c1
    c5
    1nn0
    5nn
    decnncl
    ccondx
    strle2
    c1
    c2
    c4
    1nn0
    2nn0
    4nn
    2lt4
    declt
    strleun
    eqbrtrri
end
