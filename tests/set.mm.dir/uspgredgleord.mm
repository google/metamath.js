include "cuspgr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "crab.mm"
include "cdom.mm"
include "wbr.mm"
include "chash.mm"
include "cfv.mm"
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
include "uspgredg2v.mm"
include "f1domg.mm"
include "mpsyl.mm"
include "hashdomi.mm"
include "syl.mm"

theorem uspgredgleord
  let ve: setvar e
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  assume usgredgleord.v: |- V = ( Vtx ` G )
  assume usgredgleord.e: |- E = ( Edg ` G )

  disjoint E e
  disjoint N e
  disjoint E f
  disjoint E x
  disjoint e f
  disjoint e x
  disjoint f x
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint f y
  disjoint x y
  disjoint N f
  disjoint N x
  disjoint N y
  disjoint e y
  disjoint V f
  disjoint V x
  disjoint V y
  assert |- ( ( G e. USPGraph /\ N e. V ) -> ( # ` { e e. E | N e. e } ) <_ ( # ` V ) )

  proof
    cG
    cuspgr
    wcel
    cN
    cV
    wcel
    wa
    #
    cN
    ve
    cv
    wcel
    ve
    cE
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
    vx
    @1
    vx
    cv
    cN
    vy
    cv
    cpr
    wceq
    vy
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
    usgredgleord.v
    cG
    cvtx
    fvex
    eqeltri
    vx
    vy
    @1
    ve
    cE
    @3
    cG
    cN
    cV
    usgredgleord.v
    usgredgleord.e
    @1
    eqid
    @3
    eqid
    uspgredg2v
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
