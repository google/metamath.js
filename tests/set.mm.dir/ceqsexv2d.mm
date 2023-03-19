include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "ceqsexv.mm"
include "biimpri.mm"
include "exsimpr.mm"
include "mp2b.mm"

theorem ceqsexv2d
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume ceqsexv2d.1: |- A e. _V
  assume ceqsexv2d.2: |- ( x = A -> ( ph <-> ps ) )
  assume ceqsexv2d.3: |- ps

  disjoint A x
  disjoint ps x
  assert |- E. x ph

  proof
    wps
    vx
    cv
    cA
    wceq
    #
    wph
    wa
    vx
    wex
    #
    wph
    vx
    wex
    ceqsexv2d.3
    @1
    wps
    wph
    wps
    vx
    cA
    ceqsexv2d.1
    ceqsexv2d.2
    ceqsexv
    biimpri
    @0
    wph
    vx
    exsimpr
    mp2b
end
