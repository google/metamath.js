include "cnbgr.mm"
include "co.mm"
include "wnel.mm"
include "csn.mm"
include "cdif.mm"
include "cpr.mm"
include "wss.mm"
include "wi.mm"
include "nbgrssovtx.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "wn.mm"
include "df-nel.mm"
include "disjsn.mm"
include "sylbb2.mm"
include "reldisj.mm"
include "syl5ib.mm"
include "ax-mp.mm"
include "prcom.mm"
include "difeq2i.mm"
include "difpr.mm"
include "eqtri.mm"
include "syl6sseqr.mm"

theorem nbgrssvwo2
  let cG: class G
  let cM: class M
  let cV: class V
  let cX: class X
  let vv: setvar v
  assume nbgrssovtx.v: |- V = ( Vtx ` G )


  assert |- ( M e/ ( G NeighbVtx X ) -> ( G NeighbVtx X ) C_ ( V \ { M , X } ) )

  proof
    cM
    cG
    cX
    cnbgr
    co
    #
    wnel
    #
    @0
    cV
    cX
    csn
    cdif
    #
    cM
    csn
    #
    cdif
    #
    cV
    cM
    cX
    cpr
    #
    cdif
    #
    @0
    @2
    wss
    #
    @1
    @0
    @4
    wss
    #
    wi
    cG
    cV
    cX
    nbgrssovtx.v
    nbgrssovtx
    @1
    @0
    @3
    cin
    c0
    wceq
    #
    @7
    @8
    @1
    cM
    @0
    wcel
    wn
    @9
    cM
    @0
    df-nel
    @0
    cM
    disjsn
    sylbb2
    @0
    @3
    @2
    reldisj
    syl5ib
    ax-mp
    @6
    cV
    cX
    cM
    cpr
    #
    cdif
    @4
    @5
    @10
    cV
    cM
    cX
    prcom
    difeq2i
    cV
    cX
    cM
    difpr
    eqtri
    syl6sseqr
end
