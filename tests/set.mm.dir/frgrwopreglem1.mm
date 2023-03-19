include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cvtx.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cv.mm"
include "wceq.mm"
include "crab.mm"
include "rabexg.mm"
include "syl5eqel.mm"
include "cdif.mm"
include "difexg.mm"
include "jca.mm"
include "ax-mp.mm"

theorem frgrwopreglem1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cG: class G
  let cK: class K
  let cV: class V
  assume frgrwopreg.v: |- V = ( Vtx ` G )
  assume frgrwopreg.d: |- D = ( VtxDeg ` G )
  assume frgrwopreg.a: |- A = { x e. V | ( D ` x ) = K }
  assume frgrwopreg.b: |- B = ( V \ A )

  disjoint V x
  assert |- ( A e. _V /\ B e. _V )

  proof
    cV
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    cV
    cG
    cvtx
    cfv
    cvv
    frgrwopreg.v
    cG
    cvtx
    fvex
    eqeltri
    @0
    @1
    @2
    @0
    cA
    vx
    cv
    cD
    cfv
    cK
    wceq
    #
    vx
    cV
    crab
    cvv
    frgrwopreg.a
    @3
    vx
    cV
    cvv
    rabexg
    syl5eqel
    @0
    cB
    cV
    cA
    cdif
    cvv
    frgrwopreg.b
    cV
    cA
    cvv
    difexg
    syl5eqel
    jca
    ax-mp
end
