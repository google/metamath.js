include "wfo.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "notbid.mm"
include "cbvfo.mm"
include "dfrex2.mm"
include "3bitr4g.mm"

theorem cbvexfo
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  assume cbvfo.1: |- ( ( F ` x ) = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint ph y
  disjoint ps x
  assert |- ( F : A -onto-> B -> ( E. x e. A ph <-> E. y e. B ps ) )

  proof
    cA
    cB
    cF
    wfo
    #
    wph
    wn
    #
    vx
    cA
    wral
    #
    wn
    wps
    wn
    #
    vy
    cB
    wral
    #
    wn
    wph
    vx
    cA
    wrex
    wps
    vy
    cB
    wrex
    @0
    @2
    @4
    @1
    @3
    vx
    vy
    cA
    cB
    cF
    vx
    cv
    cF
    cfv
    vy
    cv
    wceq
    wph
    wps
    cbvfo.1
    notbid
    cbvfo
    notbid
    wph
    vx
    cA
    dfrex2
    wps
    vy
    cB
    dfrex2
    3bitr4g
end
