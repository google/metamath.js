include "cuhgr.mm"
include "wcel.mm"
include "cdm.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "isuhgr.mm"
include "ibi.mm"

theorem uhgrf
  let cE: class E
  let cG: class G
  let cV: class V
  assume uhgrf.v: |- V = ( Vtx ` G )
  assume uhgrf.e: |- E = ( iEdg ` G )


  assert |- ( G e. UHGraph -> E : dom E --> ( ~P V \ { (/) } ) )

  proof
    cG
    cuhgr
    wcel
    cE
    cdm
    cV
    cpw
    c0
    csn
    cdif
    cE
    wf
    cuhgr
    cE
    cG
    cV
    uhgrf.v
    uhgrf.e
    isuhgr
    ibi
end
