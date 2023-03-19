include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cc0.mm"
include "cvtx.mm"
include "eleq2i.mm"
include "fveq2.mm"
include "vtxval0.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "syl5bb.mm"
include "noel.mm"
include "pm2.21i.mm"
include "syl6bi.mm"
include "imp.mm"

theorem vtxdg0v
  let cU: class U
  let cG: class G
  let cV: class V
  let vu: setvar u
  let vx: setvar x
  let cW: class W
  assume vtxdgf.v: |- V = ( Vtx ` G )


  assert |- ( ( G = (/) /\ U e. V ) -> ( ( VtxDeg ` G ) ` U ) = 0 )

  proof
    cG
    c0
    wceq
    #
    cU
    cV
    wcel
    #
    cU
    cG
    cvtxdg
    cfv
    cfv
    cc0
    wceq
    #
    @0
    @1
    cU
    c0
    wcel
    #
    @2
    @1
    cU
    cG
    cvtx
    cfv
    #
    wcel
    @0
    @3
    cV
    @4
    cU
    vtxdgf.v
    eleq2i
    @0
    @4
    c0
    cU
    @0
    @4
    c0
    cvtx
    cfv
    c0
    cG
    c0
    cvtx
    fveq2
    vtxval0
    syl6eq
    eleq2d
    syl5bb
    @3
    @2
    cU
    noel
    pm2.21i
    syl6bi
    imp
end
