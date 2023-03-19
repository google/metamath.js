include "cusgr.mm"
include "wcel.mm"
include "cumgr.mm"
include "cv.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "cdm.mm"
include "crab.mm"
include "c0.mm"
include "usgrumgr.mm"
include "umgrnloop0.mm"
include "syl.mm"

theorem usgrnloop0
  let vx: setvar x
  let cU: class U
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  assume usgrnloopv.e: |- E = ( iEdg ` G )

  disjoint G x
  disjoint U x
  disjoint M x
  disjoint N x
  assert |- ( G e. USGraph -> { x e. dom E | ( E ` x ) = { U } } = (/) )

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
    cU
    csn
    wceq
    vx
    cE
    cdm
    crab
    c0
    wceq
    cG
    usgrumgr
    vx
    cU
    cE
    cG
    usgrnloopv.e
    umgrnloop0
    syl
end
