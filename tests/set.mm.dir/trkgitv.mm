include "citv.mm"
include "c1.mm"
include "c6.mm"
include "cdc.mm"
include "cop.mm"
include "trkgstr.mm"
include "itvid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cbs.mm"
include "cds.mm"
include "ctp.mm"
include "snsstp3.mm"
include "sseqtr4i.mm"
include "strfv.mm"

theorem trkgitv
  let cD: class D
  let cU: class U
  let cI: class I
  let cV: class V
  let cW: class W
  assume trkgstr.w: |- W = { <. ( Base ` ndx ) , U >. , <. ( dist ` ndx ) , D >. , <. ( Itv ` ndx ) , I >. }


  assert |- ( I e. V -> I = ( Itv ` W ) )

  proof
    cI
    cW
    citv
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
    itvid
    cnx
    citv
    cfv
    cI
    cop
    #
    csn
    cnx
    cbs
    cfv
    cU
    cop
    #
    cnx
    cds
    cfv
    cD
    cop
    #
    @0
    ctp
    cW
    @1
    @2
    @0
    snsstp3
    trkgstr.w
    sseqtr4i
    strfv
end
