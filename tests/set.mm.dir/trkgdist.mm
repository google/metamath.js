include "cds.mm"
include "c1.mm"
include "c6.mm"
include "cdc.mm"
include "cop.mm"
include "trkgstr.mm"
include "dsid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cbs.mm"
include "citv.mm"
include "ctp.mm"
include "snsstp2.mm"
include "sseqtr4i.mm"
include "strfv.mm"

theorem trkgdist
  let cD: class D
  let cU: class U
  let cI: class I
  let cV: class V
  let cW: class W
  assume trkgstr.w: |- W = { <. ( Base ` ndx ) , U >. , <. ( dist ` ndx ) , D >. , <. ( Itv ` ndx ) , I >. }


  assert |- ( D e. V -> D = ( dist ` W ) )

  proof
    cD
    cW
    cds
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
    dsid
    cnx
    cds
    cfv
    cD
    cop
    #
    csn
    cnx
    cbs
    cfv
    cU
    cop
    #
    @0
    cnx
    citv
    cfv
    cI
    cop
    #
    ctp
    cW
    @1
    @0
    @2
    snsstp2
    trkgstr.w
    sseqtr4i
    strfv
end
