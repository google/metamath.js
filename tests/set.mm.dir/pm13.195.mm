include "wsbc.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "sbc5.mm"
include "bicomi.mm"

theorem pm13.195
  let wph: wff ph
  let vy: setvar y
  let cA: class A

  disjoint A y
  assert |- ( E. y ( y = A /\ ph ) <-> [. A / y ]. ph )

  proof
    wph
    vy
    cA
    wsbc
    vy
    cv
    cA
    wceq
    wph
    wa
    vy
    wex
    wph
    vy
    cA
    sbc5
    bicomi
end
