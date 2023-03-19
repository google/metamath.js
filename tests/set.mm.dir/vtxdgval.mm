include "wcel.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cv.mm"
include "crab.mm"
include "chash.mm"
include "csn.mm"
include "wceq.mm"
include "cxad.mm"
include "co.mm"
include "cmpt.mm"
include "cvv.mm"
include "1vgrex.mm"
include "vtxdgfval.mm"
include "syl.mm"
include "fveq1d.mm"
include "eleq1.mm"
include "rabbidv.mm"
include "fveq2d.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "eqtrd.mm"

theorem vtxdgval
  let vx: setvar x
  let cA: class A
  let cU: class U
  let cG: class G
  let cI: class I
  let cV: class V
  let vu: setvar u
  assume vtxdgval.v: |- V = ( Vtx ` G )
  assume vtxdgval.i: |- I = ( iEdg ` G )
  assume vtxdgval.a: |- A = dom I

  disjoint A x
  disjoint G x
  disjoint U x
  disjoint A u
  disjoint u x
  disjoint G u
  disjoint I u
  disjoint U u
  disjoint V u
  assert |- ( U e. V -> ( ( VtxDeg ` G ) ` U ) = ( ( # ` { x e. A | U e. ( I ` x ) } ) +e ( # ` { x e. A | ( I ` x ) = { U } } ) ) )

  proof
    cU
    cV
    wcel
    #
    cU
    cG
    cvtxdg
    cfv
    #
    cfv
    cU
    vu
    cV
    vu
    cv
    #
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
    @3
    @2
    csn
    #
    wceq
    #
    vx
    cA
    crab
    #
    chash
    cfv
    #
    cxad
    co
    #
    cmpt
    #
    cfv
    cU
    @3
    wcel
    #
    vx
    cA
    crab
    #
    chash
    cfv
    #
    @3
    cU
    csn
    #
    wceq
    #
    vx
    cA
    crab
    #
    chash
    cfv
    #
    cxad
    co
    #
    @0
    cU
    @1
    @12
    @0
    cG
    cvv
    wcel
    @1
    @12
    wceq
    cG
    cU
    cV
    vtxdgval.v
    1vgrex
    vx
    vu
    cA
    cG
    cI
    cV
    cvv
    vtxdgval.v
    vtxdgval.i
    vtxdgval.a
    vtxdgfval
    syl
    fveq1d
    vu
    cU
    @11
    @20
    cV
    @12
    @2
    cU
    wceq
    #
    @6
    @15
    @10
    @19
    cxad
    @21
    @5
    @14
    chash
    @21
    @4
    @13
    vx
    cA
    @2
    cU
    @3
    eleq1
    rabbidv
    fveq2d
    @21
    @9
    @18
    chash
    @21
    @8
    @17
    vx
    cA
    @21
    @7
    @16
    @3
    @2
    cU
    sneq
    eqeq2d
    rabbidv
    fveq2d
    oveq12d
    @12
    eqid
    @15
    @19
    cxad
    ovex
    fvmpt
    eqtrd
end
