include "cbs.mm"
include "c1.mm"
include "c6.mm"
include "cdc.mm"
include "cop.mm"
include "trkgstr.mm"
include "baseid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cds.mm"
include "citv.mm"
include "ctp.mm"
include "snsstp1.mm"
include "sseqtr4i.mm"
include "strfv.mm"

theorem trkgbas
  let cD: class D
  let cU: class U
  let cI: class I
  let cV: class V
  let cW: class W
  assume trkgstr.w: |- W = { <. ( Base ` ndx ) , U >. , <. ( dist ` ndx ) , D >. , <. ( Itv ` ndx ) , I >. }


  assert |- ( U e. V -> U = ( Base ` W ) )

  proof
    cU
    cW
    cbs
    cV
    c1
    c1
    c6
    cdc
    cop
    cD
    cU
    cI
    cW
    trkgstr.w
    trkgstr
    baseid
    cnx
    cbs
    cfv
    cU
    cop
    #
    csn
    @0
    cnx
    cds
    cfv
    cD
    cop
    #
    cnx
    citv
    cfv
    cI
    cop
    #
    ctp
    cW
    @0
    @1
    @2
    snsstp1
    trkgstr.w
    sseqtr4i
    strfv
end
