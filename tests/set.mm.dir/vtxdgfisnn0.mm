include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cv.mm"
include "crab.mm"
include "chash.mm"
include "csn.mm"
include "wceq.mm"
include "caddc.mm"
include "co.mm"
include "cn0.mm"
include "vtxdgfival.mm"
include "rabfi.mm"
include "hashcl.mm"
include "syl.mm"
include "nn0addcld.mm"
include "adantr.mm"
include "eqeltrd.mm"

theorem vtxdgfisnn0
  let cA: class A
  let cU: class U
  let cG: class G
  let cI: class I
  let cV: class V
  let vu: setvar u
  let vx: setvar x
  let cW: class W
  assume vtxdgf.v: |- V = ( Vtx ` G )
  assume vtxdg0e.i: |- I = ( iEdg ` G )
  assume vtxdgfisnn0.a: |- A = dom I


  assert |- ( ( A e. Fin /\ U e. V ) -> ( ( VtxDeg ` G ) ` U ) e. NN0 )

  proof
    cA
    cfn
    wcel
    #
    cU
    cV
    wcel
    #
    wa
    cU
    cG
    cvtxdg
    cfv
    cfv
    cU
    vx
    cv
    cI
    cfv
    #
    wcel
    #
    vx
    cA
    crab
    #
    chash
    cfv
    #
    @2
    cU
    csn
    wceq
    #
    vx
    cA
    crab
    #
    chash
    cfv
    #
    caddc
    co
    #
    cn0
    vx
    cA
    cU
    cG
    cI
    cV
    vtxdgf.v
    vtxdg0e.i
    vtxdgfisnn0.a
    vtxdgfival
    @0
    @9
    cn0
    wcel
    @1
    @0
    @5
    @8
    @0
    @4
    cfn
    wcel
    @5
    cn0
    wcel
    @3
    vx
    cA
    rabfi
    @4
    hashcl
    syl
    @0
    @7
    cfn
    wcel
    @8
    cn0
    wcel
    @6
    vx
    cA
    rabfi
    @7
    hashcl
    syl
    nn0addcld
    adantr
    eqeltrd
end
