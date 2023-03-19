include "cbs.mm"
include "c1.mm"
include "c4.mm"
include "cop.mm"
include "srngfn.mm"
include "baseid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "snsstp1.mm"
include "cstv.mm"
include "cun.mm"
include "ssun1.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "strfv.mm"

theorem srngbase
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let c.as: class .*
  let cX: class X
  assume srngfn.r: |- R = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .x. >. } u. { <. ( *r ` ndx ) , .* >. } )


  assert |- ( B e. X -> B = ( Base ` R ) )

  proof
    cB
    cR
    cbs
    cX
    c1
    c4
    cop
    cB
    c.pl
    cR
    c.x
    c.as
    srngfn.r
    srngfn
    baseid
    cnx
    cbs
    cfv
    cB
    cop
    #
    csn
    @0
    cnx
    cplusg
    cfv
    c.pl
    cop
    #
    cnx
    cmulr
    cfv
    c.x
    cop
    #
    ctp
    #
    cR
    @0
    @1
    @2
    snsstp1
    @3
    @3
    cnx
    cstv
    cfv
    c.as
    cop
    csn
    #
    cun
    cR
    @3
    @4
    ssun1
    srngfn.r
    sseqtr4i
    sstri
    strfv
end
