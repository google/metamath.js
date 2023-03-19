include "wfun.mm"
include "cdm.mm"
include "wss.mm"
include "wa.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "nffun.mm"
include "nfdm.mm"
include "nfss.mm"
include "nfan.mm"
include "nfima.mm"
include "funfvima2.mm"
include "ssel.mm"
include "sylan9.mm"
include "ralrimi.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "dfimafnf.mm"
include "adantr.mm"
include "abrexss.mm"
include "adantl.mm"
include "eqsstrd.mm"
include "impbida.mm"

theorem funimass4f
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y
  assume funimass4f.1: |- F/_ x A
  assume funimass4f.2: |- F/_ x B
  assume funimass4f.3: |- F/_ x F


  assert |- ( ( Fun F /\ A C_ dom F ) -> ( ( F " A ) C_ B <-> A. x e. A ( F ` x ) e. B ) )

  proof
    cF
    wfun
    #
    cA
    cF
    cdm
    #
    wss
    #
    wa
    #
    cF
    cA
    cima
    #
    cB
    wss
    #
    vx
    cv
    #
    cF
    cfv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    #
    @3
    @5
    wa
    @8
    vx
    cA
    @3
    @5
    vx
    @0
    @2
    vx
    vx
    cF
    funimass4f.3
    nffun
    vx
    cA
    @1
    funimass4f.1
    vx
    cF
    funimass4f.3
    nfdm
    nfss
    nfan
    vx
    @4
    cB
    vx
    cF
    cA
    funimass4f.3
    funimass4f.1
    nfima
    funimass4f.2
    nfss
    nfan
    @3
    @6
    cA
    wcel
    @7
    @4
    wcel
    @5
    @8
    cA
    @6
    cF
    funfvima2
    @4
    cB
    @7
    ssel
    sylan9
    ralrimi
    @3
    @9
    wa
    @4
    vy
    cv
    @7
    wceq
    vx
    cA
    wrex
    vy
    cab
    #
    cB
    @3
    @4
    @10
    wceq
    @9
    vx
    vy
    cA
    cF
    funimass4f.1
    funimass4f.3
    dfimafnf
    adantr
    @9
    @10
    cB
    wss
    @3
    vx
    vy
    cA
    @7
    cB
    funimass4f.2
    abrexss
    adantl
    eqsstrd
    impbida
end
