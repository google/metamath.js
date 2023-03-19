include "cplusg.mm"
include "c1.mm"
include "c9.mm"
include "cop.mm"
include "topgrpstr.mm"
include "plusgid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cbs.mm"
include "cts.mm"
include "ctp.mm"
include "snsstp2.mm"
include "sseqtr4i.mm"
include "strfv.mm"

theorem topgrpplusg
  let cB: class B
  let c.pl: class .+
  let cJ: class J
  let cW: class W
  let cX: class X
  assume topgrpfn.w: |- W = { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( TopSet ` ndx ) , J >. }


  assert |- ( .+ e. X -> .+ = ( +g ` W ) )

  proof
    c.pl
    cW
    cplusg
    cX
    c1
    c9
    cop
    cB
    c.pl
    cJ
    cW
    topgrpfn.w
    topgrpstr
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
    cts
    cfv
    cJ
    cop
    #
    ctp
    cW
    @1
    @0
    @2
    snsstp2
    topgrpfn.w
    sseqtr4i
    strfv
end
