include "cusgr.mm"
include "wcel.mm"
include "cumgr.mm"
include "cv.mm"
include "cfv.mm"
include "cpr.mm"
include "wceq.mm"
include "cdm.mm"
include "wrex.mm"
include "wne.mm"
include "wi.mm"
include "usgrumgr.mm"
include "umgrnloop.mm"
include "syl.mm"

theorem usgrnloop
  let vx: setvar x
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  assume usgrnloopv.e: |- E = ( iEdg ` G )

  disjoint G x
  disjoint M x
  disjoint N x
  assert |- ( G e. USGraph -> ( E. x e. dom E ( E ` x ) = { M , N } -> M =/= N ) )

  proof
    cG
    cusgr
    wcel
    cG
    cumgr
    wcel
    vx
    cv
    cE
    cfv
    cM
    cN
    cpr
    wceq
    vx
    cE
    cdm
    wrex
    cM
    cN
    wne
    wi
    cG
    usgrumgr
    vx
    cE
    cG
    cM
    cN
    usgrnloopv.e
    umgrnloop
    syl
end
