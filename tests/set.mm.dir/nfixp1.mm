include "cixp.mm"
include "cv.mm"
include "wcel.mm"
include "cab.mm"
include "wfn.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "df-ixp.mm"
include "nfcv.mm"
include "nfab1.mm"
include "nffn.mm"
include "nfra1.mm"
include "nfan.mm"
include "nfab.mm"
include "nfcxfr.mm"

theorem nfixp1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y


  assert |- F/_ x X_ x e. A B

  proof
    vx
    vx
    cA
    cB
    cixp
    vy
    cv
    #
    vx
    cv
    #
    cA
    wcel
    #
    vx
    cab
    #
    wfn
    #
    @1
    @0
    cfv
    cB
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    vy
    cab
    vx
    cA
    cB
    vy
    df-ixp
    @7
    vx
    vy
    @4
    @6
    vx
    vx
    @3
    @0
    vx
    @0
    nfcv
    @2
    vx
    nfab1
    nffn
    @5
    vx
    cA
    nfra1
    nfan
    nfab
    nfcxfr
end
