include "wsbc.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "sbcco.mm"
include "sbc5.mm"
include "bitr3i.mm"

theorem sbc7
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint A y
  disjoint ph y
  disjoint x y
  assert |- ( [. A / x ]. ph <-> E. y ( y = A /\ [. y / x ]. ph ) )

  proof
    wph
    vx
    cA
    wsbc
    wph
    vx
    vy
    cv
    #
    wsbc
    #
    vy
    cA
    wsbc
    @0
    cA
    wceq
    @1
    wa
    vy
    wex
    wph
    vx
    vy
    cA
    sbcco
    @1
    vy
    cA
    sbc5
    bitr3i
end
