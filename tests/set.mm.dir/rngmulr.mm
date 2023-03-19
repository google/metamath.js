include "cmulr.mm"
include "c1.mm"
include "c3.mm"
include "cop.mm"
include "rngstr.mm"
include "mulrid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cbs.mm"
include "cplusg.mm"
include "ctp.mm"
include "snsstp3.mm"
include "sseqtr4i.mm"
include "strfv.mm"

theorem rngmulr
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cV: class V
  assume rngfn.r: |- R = { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .x. >. }


  assert |- ( .x. e. V -> .x. = ( .r ` R ) )

  proof
    c.x
    cR
    cmulr
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
    mulrid
    cnx
    cmulr
    cfv
    c.x
    cop
    #
    csn
    cnx
    cbs
    cfv
    cB
    cop
    #
    cnx
    cplusg
    cfv
    c.pl
    cop
    #
    @0
    ctp
    cR
    @1
    @2
    @0
    snsstp3
    rngfn.r
    sseqtr4i
    strfv
end
