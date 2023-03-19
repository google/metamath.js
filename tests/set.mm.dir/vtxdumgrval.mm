include "cumgr.mm"
include "wcel.mm"
include "c2.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "crab.mm"
include "wf.mm"
include "wceq.mm"
include "cupgr.mm"
include "cdm.mm"
include "wa.mm"
include "umgrislfupgr.mm"
include "eqcomi.mm"
include "feq2i.mm"
include "biimpi.mm"
include "adantl.mm"
include "sylbi.mm"
include "vtxdlfgrval.mm"
include "sylan.mm"

theorem vtxdumgrval
  let vx: setvar x
  let cA: class A
  let cD: class D
  let cU: class U
  let cG: class G
  let cI: class I
  let cV: class V
  assume vtxdlfgrval.v: |- V = ( Vtx ` G )
  assume vtxdlfgrval.i: |- I = ( iEdg ` G )
  assume vtxdlfgrval.a: |- A = dom I
  assume vtxdlfgrval.d: |- D = ( VtxDeg ` G )

  disjoint A x
  disjoint G x
  disjoint I x
  disjoint U x
  disjoint V x
  assert |- ( ( G e. UMGraph /\ U e. V ) -> ( D ` U ) = ( # ` { x e. A | U e. ( I ` x ) } ) )

  proof
    cG
    cumgr
    wcel
    #
    cA
    c2
    vx
    cv
    #
    chash
    cfv
    cle
    wbr
    vx
    cV
    cpw
    crab
    #
    cI
    wf
    #
    cU
    cV
    wcel
    cU
    cD
    cfv
    cU
    @1
    cI
    cfv
    wcel
    vx
    cA
    crab
    chash
    cfv
    wceq
    @0
    cG
    cupgr
    wcel
    #
    cI
    cdm
    #
    @2
    cI
    wf
    #
    wa
    @3
    vx
    cG
    cI
    cV
    vtxdlfgrval.v
    vtxdlfgrval.i
    umgrislfupgr
    @6
    @3
    @4
    @6
    @3
    @5
    cA
    @2
    cI
    cA
    @5
    vtxdlfgrval.a
    eqcomi
    feq2i
    biimpi
    adantl
    sylbi
    vx
    cA
    cD
    cU
    cG
    cI
    cV
    vtxdlfgrval.v
    vtxdlfgrval.i
    vtxdlfgrval.a
    vtxdlfgrval.d
    vtxdlfgrval
    sylan
end
