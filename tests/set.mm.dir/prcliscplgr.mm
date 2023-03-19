include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "cvtx.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "cuvtx.mm"
include "wral.mm"
include "fvprc.mm"
include "eqeq1i.mm"
include "ral0.mm"
include "raleq.mm"
include "mpbiri.mm"
include "sylbir.mm"
include "syl.mm"

theorem prcliscplgr
  let vv: setvar v
  let cG: class G
  let cV: class V
  let vg: setvar g
  assume cplgruvtxb.v: |- V = ( Vtx ` G )

  disjoint G v
  disjoint V v
  disjoint G g
  disjoint V g
  disjoint g v
  assert |- ( -. G e. _V -> A. v e. V v e. ( UnivVtx ` G ) )

  proof
    cG
    cvv
    wcel
    wn
    cG
    cvtx
    cfv
    #
    c0
    wceq
    #
    vv
    cv
    cG
    cuvtx
    cfv
    wcel
    #
    vv
    cV
    wral
    #
    cG
    cvtx
    fvprc
    @1
    cV
    c0
    wceq
    #
    @3
    cV
    @0
    c0
    cplgruvtxb.v
    eqeq1i
    @4
    @3
    @2
    vv
    c0
    wral
    @2
    vv
    ral0
    @2
    vv
    cV
    c0
    raleq
    mpbiri
    sylbir
    syl
end
