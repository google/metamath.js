include "cushgr.mm"
include "wcel.mm"
include "cdm.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf1.mm"
include "isushgr.mm"
include "ibi.mm"

theorem ushgrf
  let cE: class E
  let cG: class G
  let cV: class V
  assume uhgrf.v: |- V = ( Vtx ` G )
  assume uhgrf.e: |- E = ( iEdg ` G )


  assert |- ( G e. USHGraph -> E : dom E -1-1-> ( ~P V \ { (/) } ) )

  proof
    cG
    cushgr
    wcel
    cE
    cdm
    cV
    cpw
    c0
    csn
    cdif
    cE
    wf1
    cushgr
    cE
    cG
    cV
    uhgrf.v
    uhgrf.e
    isushgr
    ibi
end
