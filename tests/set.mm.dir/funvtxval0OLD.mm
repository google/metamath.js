include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "wne.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "wa.mm"
include "cpr.mm"
include "cdm.mm"
include "wss.mm"
include "cvtx.mm"
include "wceq.mm"
include "necom.mm"
include "fvex.mm"
include "funvtxdm2valOLD.mm"
include "syl3an2b.mm"

theorem funvtxval0OLD
  let cS: class S
  let cG: class G
  let cV: class V
  assume funvtxval0.s: |- S e. _V


  assert |- ( ( ( G e. V /\ Fun ( G \ { (/) } ) ) /\ S =/= ( Base ` ndx ) /\ { ( Base ` ndx ) , S } C_ dom G ) -> ( Vtx ` G ) = ( Base ` G ) )

  proof
    cS
    cnx
    cbs
    cfv
    #
    wne
    cG
    cV
    wcel
    cG
    c0
    csn
    cdif
    wfun
    wa
    @0
    cS
    wne
    @0
    cS
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
    cS
    @0
    necom
    @0
    cS
    cG
    cV
    cnx
    cbs
    fvex
    funvtxval0.s
    funvtxdm2valOLD
    syl3an2b
end
