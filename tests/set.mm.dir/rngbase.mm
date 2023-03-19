include "cbs.mm"
include "c1.mm"
include "c3.mm"
include "cop.mm"
include "rngstr.mm"
include "baseid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "snsstp1.mm"
include "sseqtr4i.mm"
include "strfv.mm"

theorem rngbase
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cV: class V
  assume rngfn.r: |- R = { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .x. >. }


  assert |- ( B e. V -> B = ( Base ` R ) )

  proof
    cB
    cR
    cbs
    cV
    c1
    c3
    cop
    cB
    c.pl
    cR
    c.x
    rngfn.r
    rngstr
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
    cR
    @0
    @1
    @2
    snsstp1
    rngfn.r
    sseqtr4i
    strfv
end
