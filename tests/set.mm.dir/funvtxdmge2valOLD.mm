include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "c2.mm"
include "cdm.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cvtx.mm"
include "cvv.mm"
include "cxp.mm"
include "c1st.mm"
include "cbs.mm"
include "cif.mm"
include "wceq.mm"
include "vtxvalOLD.mm"
include "3ad2ant1.mm"
include "wn.mm"
include "fundmge2nop0.mm"
include "3adant1.mm"
include "iffalsed.mm"
include "eqtrd.mm"

theorem funvtxdmge2valOLD
  let cG: class G
  let cV: class V


  assert |- ( ( G e. V /\ Fun ( G \ { (/) } ) /\ 2 <_ ( # ` dom G ) ) -> ( Vtx ` G ) = ( Base ` G ) )

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
    c2
    cG
    cdm
    chash
    cfv
    cle
    wbr
    #
    w3a
    #
    cG
    cvtx
    cfv
    #
    cG
    cvv
    cvv
    cxp
    wcel
    #
    cG
    c1st
    cfv
    #
    cG
    cbs
    cfv
    #
    cif
    #
    @7
    @0
    @1
    @4
    @8
    wceq
    @2
    cG
    cV
    vtxvalOLD
    3ad2ant1
    @3
    @5
    @6
    @7
    @1
    @2
    @5
    wn
    @0
    cG
    fundmge2nop0
    3adant1
    iffalsed
    eqtrd
end
