include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "biimpac.mm"
include "exlimiv.mm"
include "impbii.mm"
include "gencbvex.mm"

theorem gencbvex2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume gencbvex2.1: |- A e. _V
  assume gencbvex2.2: |- ( A = y -> ( ph <-> ps ) )
  assume gencbvex2.3: |- ( A = y -> ( ch <-> th ) )
  assume gencbvex2.4: |- ( th -> E. x ( ch /\ A = y ) )

  disjoint ps x
  disjoint ph y
  disjoint th x
  disjoint ch y
  disjoint A y
  assert |- ( E. x ( ch /\ ph ) <-> E. y ( th /\ ps ) )

  proof
    wph
    wps
    wch
    wth
    vx
    vy
    cA
    gencbvex2.1
    gencbvex2.2
    gencbvex2.3
    wth
    wch
    cA
    vy
    cv
    wceq
    #
    wa
    #
    vx
    wex
    gencbvex2.4
    @1
    wth
    vx
    @0
    wch
    wth
    gencbvex2.3
    biimpac
    exlimiv
    impbii
    gencbvex
end
