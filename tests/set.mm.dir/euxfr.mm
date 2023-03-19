include "weu.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "euex.mm"
include "ax-mp.mm"
include "biantrur.mm"
include "19.41v.mm"
include "pm5.32i.mm"
include "exbii.mm"
include "3bitr2i.mm"
include "eubii.mm"
include "eumoi.mm"
include "euxfr2.mm"
include "bitri.mm"

theorem euxfr
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume euxfr.1: |- A e. _V
  assume euxfr.2: |- E! y x = A
  assume euxfr.3: |- ( x = A -> ( ph <-> ps ) )

  disjoint ps x
  disjoint ph y
  disjoint A x
  assert |- ( E! x ph <-> E! y ps )

  proof
    wph
    vx
    weu
    vx
    cv
    cA
    wceq
    #
    wps
    wa
    #
    vy
    wex
    #
    vx
    weu
    wps
    vy
    weu
    wph
    @2
    vx
    wph
    @0
    vy
    wex
    #
    wph
    wa
    @0
    wph
    wa
    #
    vy
    wex
    @2
    @3
    wph
    @0
    vy
    weu
    @3
    euxfr.2
    @0
    vy
    euex
    ax-mp
    biantrur
    @0
    wph
    vy
    19.41v
    @4
    @1
    vy
    @0
    wph
    wps
    euxfr.3
    pm5.32i
    exbii
    3bitr2i
    eubii
    wps
    vx
    vy
    cA
    euxfr.1
    @0
    vy
    euxfr.2
    eumoi
    euxfr2
    bitri
end
