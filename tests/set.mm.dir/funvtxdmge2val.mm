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
include "wa.mm"
include "cvtx.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "c1st.mm"
include "cbs.mm"
include "cif.mm"
include "vtxval.mm"
include "fundmge2nop0.mm"
include "iffalsed.mm"
include "syl5eq.mm"

theorem funvtxdmge2val
  let cG: class G


  assert |- ( ( Fun ( G \ { (/) } ) /\ 2 <_ ( # ` dom G ) ) -> ( Vtx ` G ) = ( Base ` G ) )

  proof
    cG
    c0
    csn
    cdif
    wfun
    c2
    cG
    cdm
    chash
    cfv
    cle
    wbr
    wa
    #
    cG
    cvtx
    cfv
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
    @3
    cG
    vtxval
    @0
    @1
    @2
    @3
    cG
    fundmge2nop0
    iffalsed
    syl5eq
end
