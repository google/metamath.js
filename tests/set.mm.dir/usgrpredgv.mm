include "cusgr.mm"
include "wcel.mm"
include "cumgr.mm"
include "cpr.mm"
include "wa.mm"
include "usgrumgr.mm"
include "umgrpredgv.mm"
include "sylan.mm"

theorem usgrpredgv
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  let cV: class V
  assume usgredgppr.e: |- E = ( Edg ` G )
  assume usgrpredgv.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. USGraph /\ { M , N } e. E ) -> ( M e. V /\ N e. V ) )

  proof
    cG
    cusgr
    wcel
    cG
    cumgr
    wcel
    cM
    cN
    cpr
    cE
    wcel
    cM
    cV
    wcel
    cN
    cV
    wcel
    wa
    cG
    usgrumgr
    cE
    cG
    cM
    cN
    cV
    usgrpredgv.v
    usgredgppr.e
    umgrpredgv
    sylan
end
