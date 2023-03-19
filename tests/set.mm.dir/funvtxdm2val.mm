include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "wne.mm"
include "cpr.mm"
include "cdm.mm"
include "wss.mm"
include "w3a.mm"
include "cvtx.mm"
include "cfv.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "c1st.mm"
include "cbs.mm"
include "cif.mm"
include "vtxval.mm"
include "fun2dmnop0.mm"
include "iffalsed.mm"
include "syl5eq.mm"

theorem funvtxdm2val
  let cA: class A
  let cB: class B
  let cG: class G
  assume funvtxdm2val.a: |- A e. _V
  assume funvtxdm2val.b: |- B e. _V


  assert |- ( ( Fun ( G \ { (/) } ) /\ A =/= B /\ { A , B } C_ dom G ) -> ( Vtx ` G ) = ( Base ` G ) )

  proof
    cG
    c0
    csn
    cdif
    wfun
    cA
    cB
    wne
    cA
    cB
    cpr
    cG
    cdm
    wss
    w3a
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
    cA
    cB
    cG
    funvtxdm2val.a
    funvtxdm2val.b
    fun2dmnop0
    iffalsed
    syl5eq
end
