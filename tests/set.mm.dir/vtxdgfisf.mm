include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "wfn.mm"
include "cv.mm"
include "cn0.mm"
include "wral.mm"
include "wf.mm"
include "cxnn0.mm"
include "vtxdgf.mm"
include "adantr.mm"
include "ffnd.mm"
include "vtxdgfisnn0.mm"
include "adantll.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"

theorem vtxdgfisf
  let cA: class A
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let vu: setvar u
  let vx: setvar x
  let cU: class U
  assume vtxdgf.v: |- V = ( Vtx ` G )
  assume vtxdg0e.i: |- I = ( iEdg ` G )
  assume vtxdgfisnn0.a: |- A = dom I


  assert |- ( ( G e. W /\ A e. Fin ) -> ( VtxDeg ` G ) : V --> NN0 )

  proof
    cG
    cW
    wcel
    #
    cA
    cfn
    wcel
    #
    wa
    #
    cG
    cvtxdg
    cfv
    #
    cV
    wfn
    vu
    cv
    #
    @3
    cfv
    cn0
    wcel
    #
    vu
    cV
    wral
    cV
    cn0
    @3
    wf
    @2
    cV
    cxnn0
    @3
    @0
    cV
    cxnn0
    @3
    wf
    @1
    cG
    cV
    cW
    vtxdgf.v
    vtxdgf
    adantr
    ffnd
    @2
    @5
    vu
    cV
    @1
    @4
    cV
    wcel
    @5
    @0
    cA
    @4
    cG
    cI
    cV
    vtxdgf.v
    vtxdg0e.i
    vtxdgfisnn0.a
    vtxdgfisnn0
    adantll
    ralrimiva
    vu
    cV
    cn0
    @3
    ffnfv
    sylanbrc
end
