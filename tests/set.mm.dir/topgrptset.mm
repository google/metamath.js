include "cts.mm"
include "c1.mm"
include "c9.mm"
include "cop.mm"
include "topgrpstr.mm"
include "tsetid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cbs.mm"
include "cplusg.mm"
include "ctp.mm"
include "snsstp3.mm"
include "sseqtr4i.mm"
include "strfv.mm"

theorem topgrptset
  let cB: class B
  let c.pl: class .+
  let cJ: class J
  let cW: class W
  let cX: class X
  assume topgrpfn.w: |- W = { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( TopSet ` ndx ) , J >. }


  assert |- ( J e. X -> J = ( TopSet ` W ) )

  proof
    cJ
    cW
    cts
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
    tsetid
    cnx
    cts
    cfv
    cJ
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
    cW
    @1
    @2
    @0
    snsstp3
    topgrpfn.w
    sseqtr4i
    strfv
end
