include "cv.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "wa.mm"
include "3anass.mm"
include "exbii.mm"
include "19.42v.mm"
include "bitri.mm"
include "nfv.mm"
include "nfan.mm"
include "nfex.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "ceqsex.mm"
include "3bitri.mm"

theorem ceqsex2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume ceqsex2.1: |- F/ x ps
  assume ceqsex2.2: |- F/ y ch
  assume ceqsex2.3: |- A e. _V
  assume ceqsex2.4: |- B e. _V
  assume ceqsex2.5: |- ( x = A -> ( ph <-> ps ) )
  assume ceqsex2.6: |- ( y = B -> ( ps <-> ch ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( E. x E. y ( x = A /\ y = B /\ ph ) <-> ch )

  proof
    vx
    cv
    cA
    wceq
    #
    vy
    cv
    cB
    wceq
    #
    wph
    w3a
    #
    vy
    wex
    #
    vx
    wex
    @0
    @1
    wph
    wa
    #
    vy
    wex
    #
    wa
    #
    vx
    wex
    @1
    wps
    wa
    #
    vy
    wex
    #
    wch
    @3
    @6
    vx
    @3
    @0
    @4
    wa
    #
    vy
    wex
    @6
    @2
    @9
    vy
    @0
    @1
    wph
    3anass
    exbii
    @0
    @4
    vy
    19.42v
    bitri
    exbii
    @5
    @8
    vx
    cA
    @7
    vx
    vy
    @1
    wps
    vx
    @1
    vx
    nfv
    ceqsex2.1
    nfan
    nfex
    ceqsex2.3
    @0
    @4
    @7
    vy
    @0
    wph
    wps
    @1
    ceqsex2.5
    anbi2d
    exbidv
    ceqsex
    wps
    wch
    vy
    cB
    ceqsex2.2
    ceqsex2.4
    ceqsex2.6
    ceqsex
    3bitri
end
