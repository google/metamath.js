include "cumgr.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cpr.mm"
include "wceq.mm"
include "wne.mm"
include "cdm.mm"
include "wa.mm"
include "cvtx.mm"
include "eqid.mm"
include "umgredgprv.mm"
include "imp.mm"
include "wi.mm"
include "umgrnloopv.mm"
include "ex.mm"
include "com23.mm"
include "adantr.mm"
include "com12.mm"
include "mpcom.mm"
include "rexlimdva.mm"

theorem umgrnloop
  let vx: setvar x
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  assume umgrnloopv.e: |- E = ( iEdg ` G )

  disjoint G x
  disjoint M x
  disjoint N x
  assert |- ( G e. UMGraph -> ( E. x e. dom E ( E ` x ) = { M , N } -> M =/= N ) )

  proof
    cG
    cumgr
    wcel
    #
    vx
    cv
    #
    cE
    cfv
    cM
    cN
    cpr
    wceq
    #
    cM
    cN
    wne
    #
    vx
    cE
    cdm
    #
    @0
    @1
    @4
    wcel
    #
    wa
    #
    @2
    @3
    cM
    cG
    cvtx
    cfv
    #
    wcel
    #
    cN
    @7
    wcel
    #
    wa
    #
    @6
    @2
    wa
    #
    @3
    @6
    @2
    @10
    cE
    cG
    cM
    cN
    @7
    @1
    umgrnloopv.e
    @7
    eqid
    umgredgprv
    imp
    @8
    @11
    @3
    wi
    @9
    @11
    @8
    @3
    @6
    @2
    @8
    @3
    wi
    #
    @0
    @2
    @12
    wi
    @5
    @0
    @8
    @2
    @3
    @0
    @8
    @2
    @3
    wi
    cE
    cG
    cM
    cN
    @7
    @1
    umgrnloopv.e
    umgrnloopv
    ex
    com23
    adantr
    imp
    com12
    adantr
    mpcom
    ex
    rexlimdva
end
