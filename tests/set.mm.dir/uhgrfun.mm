include "cuhgr.mm"
include "wcel.mm"
include "cdm.mm"
include "cvtx.mm"
include "cfv.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "eqid.mm"
include "uhgrf.mm"
include "ffund.mm"

theorem uhgrfun
  let cE: class E
  let cG: class G
  assume uhgrfun.e: |- E = ( iEdg ` G )


  assert |- ( G e. UHGraph -> Fun E )

  proof
    cG
    cuhgr
    wcel
    cE
    cdm
    cG
    cvtx
    cfv
    #
    cpw
    c0
    csn
    cdif
    cE
    cE
    cG
    @0
    @0
    eqid
    uhgrfun.e
    uhgrf
    ffund
end
