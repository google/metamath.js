include "cusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cdm.mm"
include "crab.mm"
include "cdom.mm"
include "wbr.mm"
include "chash.mm"
include "cle.mm"
include "cvv.mm"
include "cpr.mm"
include "wceq.mm"
include "crio.mm"
include "cmpt.mm"
include "wf1.mm"
include "cvtx.mm"
include "fvex.mm"
include "eqeltri.mm"
include "eqid.mm"
include "usgredg2v.mm"
include "f1domg.mm"
include "mpsyl.mm"
include "hashdomi.mm"
include "syl.mm"

theorem usgriedgleord
  let vx: setvar x
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let vz: setvar z
  let vy: setvar y
  assume usgredg2v.v: |- V = ( Vtx ` G )
  assume usgredg2v.e: |- E = ( iEdg ` G )

  disjoint E x
  disjoint N x
  disjoint E z
  disjoint x z
  disjoint G z
  disjoint N z
  disjoint V z
  disjoint E y
  disjoint x y
  disjoint y z
  disjoint G y
  disjoint N y
  disjoint V y
  assert |- ( ( G e. USGraph /\ N e. V ) -> ( # ` { x e. dom E | N e. ( E ` x ) } ) <_ ( # ` V ) )

  proof
    cG
    cusgr
    wcel
    cN
    cV
    wcel
    wa
    #
    cN
    vx
    cv
    cE
    cfv
    wcel
    vx
    cE
    cdm
    crab
    #
    cV
    cdom
    wbr
    #
    @1
    chash
    cfv
    cV
    chash
    cfv
    cle
    wbr
    cV
    cvv
    wcel
    @0
    @1
    cV
    vy
    @1
    vy
    cv
    cE
    cfv
    vz
    cv
    cN
    cpr
    wceq
    vz
    cV
    crio
    cmpt
    #
    wf1
    @2
    cV
    cG
    cvtx
    cfv
    cvv
    usgredg2v.v
    cG
    cvtx
    fvex
    eqeltri
    vx
    vy
    vz
    @1
    cE
    @3
    cG
    cN
    cV
    usgredg2v.v
    usgredg2v.e
    @1
    eqid
    @3
    eqid
    usgredg2v
    @1
    cV
    cvv
    @3
    f1domg
    mpsyl
    @1
    cV
    hashdomi
    syl
end
