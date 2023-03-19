include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cedgf.mm"
include "cpr.mm"
include "cdm.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "ciedg.mm"
include "wceq.mm"
include "3simpa.mm"
include "slotsbaseefdif.mm"
include "a1i.mm"
include "simp3.mm"
include "fvex.mm"
include "funiedgdm2valOLD.mm"
include "syl3anc.mm"

theorem funiedgvalOLD
  let cG: class G
  let cV: class V


  assert |- ( ( G e. V /\ Fun ( G \ { (/) } ) /\ { ( Base ` ndx ) , ( .ef ` ndx ) } C_ dom G ) -> ( iEdg ` G ) = ( .ef ` G ) )

  proof
    cG
    cV
    wcel
    #
    cG
    c0
    csn
    cdif
    wfun
    #
    cnx
    cbs
    cfv
    #
    cnx
    cedgf
    cfv
    #
    cpr
    cG
    cdm
    wss
    #
    w3a
    #
    @0
    @1
    wa
    @2
    @3
    wne
    #
    @4
    cG
    ciedg
    cfv
    cG
    cedgf
    cfv
    wceq
    @0
    @1
    @4
    3simpa
    @6
    @5
    slotsbaseefdif
    a1i
    @0
    @1
    @4
    simp3
    @2
    @3
    cG
    cV
    cnx
    cbs
    fvex
    cnx
    cedgf
    fvex
    funiedgdm2valOLD
    syl3anc
end
