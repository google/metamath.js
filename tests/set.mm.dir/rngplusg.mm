include "cplusg.mm"
include "c1.mm"
include "c3.mm"
include "cop.mm"
include "rngstr.mm"
include "plusgid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cbs.mm"
include "cmulr.mm"
include "ctp.mm"
include "snsstp2.mm"
include "sseqtr4i.mm"
include "strfv.mm"

theorem rngplusg
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cV: class V
  assume rngfn.r: |- R = { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .x. >. }


  assert |- ( .+ e. V -> .+ = ( +g ` R ) )

  proof
    c.pl
    cR
    cplusg
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
    c.x
    cop
    #
    ctp
    cR
    @1
    @0
    @2
    snsstp2
    rngfn.r
    sseqtr4i
    strfv
end
