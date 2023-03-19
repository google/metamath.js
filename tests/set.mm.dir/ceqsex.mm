include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "biimpa.mm"
include "exlimi.mm"
include "wi.mm"
include "wal.mm"
include "biimprcd.mm"
include "alrimi.mm"
include "isseti.mm"
include "exintr.mm"
include "mpisyl.mm"
include "impbii.mm"

theorem ceqsex
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume ceqsex.1: |- F/ x ps
  assume ceqsex.2: |- A e. _V
  assume ceqsex.3: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  assert |- ( E. x ( x = A /\ ph ) <-> ps )

  proof
    vx
    cv
    cA
    wceq
    #
    wph
    wa
    #
    vx
    wex
    #
    wps
    @1
    wps
    vx
    ceqsex.1
    @0
    wph
    wps
    ceqsex.3
    biimpa
    exlimi
    wps
    @0
    wph
    wi
    #
    vx
    wal
    @0
    vx
    wex
    @2
    wps
    @3
    vx
    ceqsex.1
    @0
    wph
    wps
    ceqsex.3
    biimprcd
    alrimi
    vx
    cA
    ceqsex.2
    isseti
    @0
    wph
    vx
    exintr
    mpisyl
    impbii
end
