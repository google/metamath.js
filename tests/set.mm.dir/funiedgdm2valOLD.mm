include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "wa.mm"
include "wne.mm"
include "cpr.mm"
include "cdm.mm"
include "wss.mm"
include "w3a.mm"
include "ciedg.mm"
include "cfv.mm"
include "cvv.mm"
include "cxp.mm"
include "c2nd.mm"
include "cedgf.mm"
include "cif.mm"
include "wceq.mm"
include "iedgvalOLD.mm"
include "adantr.mm"
include "3ad2ant1.mm"
include "wn.mm"
include "fun2dmnop0.mm"
include "3adant1l.mm"
include "iffalsed.mm"
include "eqtrd.mm"

theorem funiedgdm2valOLD
  let cA: class A
  let cB: class B
  let cG: class G
  let cV: class V
  assume funvtxdm2val.a: |- A e. _V
  assume funvtxdm2val.b: |- B e. _V


  assert |- ( ( ( G e. V /\ Fun ( G \ { (/) } ) ) /\ A =/= B /\ { A , B } C_ dom G ) -> ( iEdg ` G ) = ( .ef ` G ) )

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
    wa
    #
    cA
    cB
    wne
    #
    cA
    cB
    cpr
    cG
    cdm
    wss
    #
    w3a
    #
    cG
    ciedg
    cfv
    #
    cG
    cvv
    cvv
    cxp
    wcel
    #
    cG
    c2nd
    cfv
    #
    cG
    cedgf
    cfv
    #
    cif
    #
    @9
    @2
    @3
    @6
    @10
    wceq
    #
    @4
    @0
    @11
    @1
    cG
    cV
    iedgvalOLD
    adantr
    3ad2ant1
    @5
    @7
    @8
    @9
    @1
    @3
    @4
    @7
    wn
    @0
    cA
    cB
    cG
    funvtxdm2val.a
    funvtxdm2val.b
    fun2dmnop0
    3adant1l
    iffalsed
    eqtrd
end
