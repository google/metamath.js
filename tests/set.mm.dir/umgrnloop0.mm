include "cumgr.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "wn.mm"
include "cdm.mm"
include "wral.mm"
include "crab.mm"
include "c0.mm"
include "wrex.mm"
include "cpr.mm"
include "wne.mm"
include "neirr.mm"
include "umgrnloop.mm"
include "mtoi.mm"
include "wa.mm"
include "simpr.mm"
include "dfsn2.mm"
include "syl6eq.mm"
include "ex.mm"
include "reximdv.mm"
include "mtod.mm"
include "ralnex.mm"
include "sylibr.mm"
include "rabeq0.mm"

theorem umgrnloop0
  let vx: setvar x
  let cU: class U
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  assume umgrnloopv.e: |- E = ( iEdg ` G )

  disjoint G x
  disjoint U x
  disjoint M x
  disjoint N x
  assert |- ( G e. UMGraph -> { x e. dom E | ( E ` x ) = { U } } = (/) )

  proof
    cG
    cumgr
    wcel
    #
    vx
    cv
    cE
    cfv
    #
    cU
    csn
    #
    wceq
    #
    wn
    vx
    cE
    cdm
    #
    wral
    #
    @3
    vx
    @4
    crab
    c0
    wceq
    @0
    @3
    vx
    @4
    wrex
    #
    wn
    @5
    @0
    @6
    @1
    cU
    cU
    cpr
    #
    wceq
    #
    vx
    @4
    wrex
    #
    @0
    @9
    cU
    cU
    wne
    cU
    neirr
    vx
    cE
    cG
    cU
    cU
    umgrnloopv.e
    umgrnloop
    mtoi
    @0
    @3
    @8
    vx
    @4
    @0
    @3
    @8
    @0
    @3
    wa
    @1
    @2
    @7
    @0
    @3
    simpr
    cU
    dfsn2
    syl6eq
    ex
    reximdv
    mtod
    @3
    vx
    @4
    ralnex
    sylibr
    @3
    vx
    @4
    rabeq0
    sylibr
end
