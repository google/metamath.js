include "cusgr.mm"
include "wcel.mm"
include "cumgr.mm"
include "cdm.mm"
include "cfv.mm"
include "cpr.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "usgrumgr.mm"
include "umgredgprv.mm"
include "sylan.mm"

theorem usgredgprv
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let vx: setvar x
  assume usgredg2.e: |- E = ( iEdg ` G )
  assume usgredgprv.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. USGraph /\ X e. dom E ) -> ( ( E ` X ) = { M , N } -> ( M e. V /\ N e. V ) ) )

  proof
    cG
    cusgr
    wcel
    cG
    cumgr
    wcel
    cX
    cE
    cdm
    wcel
    cX
    cE
    cfv
    cM
    cN
    cpr
    wceq
    cM
    cV
    wcel
    cN
    cV
    wcel
    wa
    wi
    cG
    usgrumgr
    cE
    cG
    cM
    cN
    cV
    cX
    usgredg2.e
    usgredgprv.v
    umgredgprv
    sylan
end
