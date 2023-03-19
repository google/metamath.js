include "wfn.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cima.mm"
include "cvv.mm"
include "wcel.mm"
include "fvexd.mm"
include "wceq.mm"
include "wrex.mm"
include "fvelimab.mm"
include "eqcom.mm"
include "rexbii.mm"
include "syl6bb.mm"
include "wb.mm"
include "adantl.mm"
include "ralxfr2d.mm"

theorem ralima
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  assume rexima.x: |- ( x = ( F ` y ) -> ( ph <-> ps ) )

  disjoint ph y
  disjoint ps x
  disjoint F x
  disjoint F y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A x
  disjoint A y
  assert |- ( ( F Fn A /\ B C_ A ) -> ( A. x e. ( F " B ) ph <-> A. y e. B ps ) )

  proof
    cF
    cA
    wfn
    cB
    cA
    wss
    wa
    #
    wph
    wps
    vx
    vy
    vy
    cv
    #
    cF
    cfv
    #
    cF
    cB
    cima
    #
    cB
    cvv
    @0
    @1
    cB
    wcel
    wa
    @1
    cF
    fvexd
    @0
    vx
    cv
    #
    @3
    wcel
    @2
    @4
    wceq
    #
    vy
    cB
    wrex
    @4
    @2
    wceq
    #
    vy
    cB
    wrex
    vy
    cA
    cB
    @4
    cF
    fvelimab
    @5
    @6
    vy
    cB
    @2
    @4
    eqcom
    rexbii
    syl6bb
    @6
    wph
    wps
    wb
    @0
    rexima.x
    adantl
    ralxfr2d
end
