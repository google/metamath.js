include "cusgr.mm"
include "wcel.mm"
include "cumgr.mm"
include "cfv.mm"
include "cpr.mm"
include "wceq.mm"
include "wne.mm"
include "wi.mm"
include "usgrumgr.mm"
include "umgrnloopv.mm"
include "sylan.mm"

theorem usgrnloopv
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  assume usgrnloopv.e: |- E = ( iEdg ` G )


  assert |- ( ( G e. USGraph /\ M e. W ) -> ( ( E ` X ) = { M , N } -> M =/= N ) )

  proof
    cG
    cusgr
    wcel
    cG
    cumgr
    wcel
    cM
    cW
    wcel
    cX
    cE
    cfv
    cM
    cN
    cpr
    wceq
    cM
    cN
    wne
    wi
    cG
    usgrumgr
    cE
    cG
    cM
    cN
    cW
    cX
    usgrnloopv.e
    umgrnloopv
    sylan
end
