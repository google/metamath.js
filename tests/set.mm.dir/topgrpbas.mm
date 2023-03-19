include "cbs.mm"
include "c1.mm"
include "c9.mm"
include "cop.mm"
include "topgrpstr.mm"
include "baseid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cplusg.mm"
include "cts.mm"
include "ctp.mm"
include "snsstp1.mm"
include "sseqtr4i.mm"
include "strfv.mm"

theorem topgrpbas
  let cB: class B
  let c.pl: class .+
  let cJ: class J
  let cW: class W
  let cX: class X
  assume topgrpfn.w: |- W = { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( TopSet ` ndx ) , J >. }


  assert |- ( B e. X -> B = ( Base ` W ) )

  proof
    cB
    cW
    cbs
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
    cts
    cfv
    cJ
    cop
    #
    ctp
    cW
    @0
    @1
    @2
    snsstp1
    topgrpfn.w
    sseqtr4i
    strfv
end
