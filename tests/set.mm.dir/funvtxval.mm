include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cedgf.mm"
include "wne.mm"
include "cpr.mm"
include "cdm.mm"
include "wss.mm"
include "cvtx.mm"
include "wceq.mm"
include "slotsbaseefdif.mm"
include "fvex.mm"
include "funvtxdm2val.mm"
include "mp3an2.mm"

theorem funvtxval
  let cG: class G


  assert |- ( ( Fun ( G \ { (/) } ) /\ { ( Base ` ndx ) , ( .ef ` ndx ) } C_ dom G ) -> ( Vtx ` G ) = ( Base ` G ) )

  proof
    cG
    c0
    csn
    cdif
    wfun
    cnx
    cbs
    cfv
    #
    cnx
    cedgf
    cfv
    #
    wne
    @0
    @1
    cpr
    cG
    cdm
    wss
    cG
    cvtx
    cfv
    cG
    cbs
    cfv
    wceq
    slotsbaseefdif
    @0
    @1
    cG
    cnx
    cbs
    fvex
    cnx
    cedgf
    fvex
    funvtxdm2val
    mp3an2
end
