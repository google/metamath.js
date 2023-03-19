include "wfun.mm"
include "cdm.mm"
include "wss.mm"
include "wa.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cab.mm"
include "ciun.mm"
include "csn.mm"
include "wrex.mm"
include "dfimafn.mm"
include "iunab.mm"
include "syl6eqr.mm"
include "wcel.mm"
include "df-sn.mm"
include "eqcom.mm"
include "abbii.mm"
include "eqtri.mm"
include "a1i.mm"
include "iuneq2i.mm"

theorem dfimafn2
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let cB: class B
  let cY: class Y

  disjoint A x
  disjoint F x
  disjoint x y
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F y
  disjoint Y x
  assert |- ( ( Fun F /\ A C_ dom F ) -> ( F " A ) = U_ x e. A { ( F ` x ) } )

  proof
    cF
    wfun
    cA
    cF
    cdm
    wss
    wa
    #
    cF
    cA
    cima
    #
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    wceq
    #
    vy
    cab
    #
    ciun
    #
    vx
    cA
    @3
    csn
    #
    ciun
    @0
    @1
    @5
    vx
    cA
    wrex
    vy
    cab
    @7
    vx
    vy
    cA
    cF
    dfimafn
    @5
    vx
    vy
    cA
    iunab
    syl6eqr
    vx
    cA
    @8
    @6
    @8
    @6
    wceq
    @2
    cA
    wcel
    @8
    @4
    @3
    wceq
    #
    vy
    cab
    @6
    vy
    @3
    df-sn
    @9
    @5
    vy
    @4
    @3
    eqcom
    abbii
    eqtri
    a1i
    iuneq2i
    syl6eqr
end
