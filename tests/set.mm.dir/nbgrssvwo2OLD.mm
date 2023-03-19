include "wcel.mm"
include "cnbgr.mm"
include "co.mm"
include "wnel.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cpr.mm"
include "wss.mm"
include "wi.mm"
include "nbgrssovtxOLD.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "df-nel.mm"
include "disjsn.mm"
include "sylbb2.mm"
include "reldisj.mm"
include "syl5ib.mm"
include "syl.mm"
include "imp.mm"
include "prcom.mm"
include "difeq2i.mm"
include "difpr.mm"
include "eqtri.mm"
include "syl6sseqr.mm"

theorem nbgrssvwo2OLD
  let cG: class G
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let vv: setvar v
  assume nbgrssovtxOLD.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. W /\ M e/ ( G NeighbVtx N ) ) -> ( G NeighbVtx N ) C_ ( V \ { M , N } ) )

  proof
    cG
    cW
    wcel
    #
    cM
    cG
    cN
    cnbgr
    co
    #
    wnel
    #
    wa
    @1
    cV
    cN
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
    cN
    cpr
    #
    cdif
    #
    @0
    @2
    @1
    @5
    wss
    #
    @0
    @1
    @3
    wss
    #
    @2
    @8
    wi
    cG
    cN
    cV
    cW
    nbgrssovtxOLD.v
    nbgrssovtxOLD
    @2
    @1
    @4
    cin
    c0
    wceq
    #
    @9
    @8
    @2
    cM
    @1
    wcel
    wn
    @10
    cM
    @1
    df-nel
    @1
    cM
    disjsn
    sylbb2
    @1
    @4
    @3
    reldisj
    syl5ib
    syl
    imp
    @7
    cV
    cN
    cM
    cpr
    #
    cdif
    @5
    @6
    @11
    cV
    cM
    cN
    prcom
    difeq2i
    cV
    cN
    cM
    difpr
    eqtri
    syl6sseqr
end
