include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "excom.mm"
include "wb.mm"
include "anbi12d.mm"
include "bicomd.mm"
include "eqcoms.mm"
include "ceqsexv.mm"
include "exbii.mm"
include "19.41v.mm"
include "simpr.mm"
include "eqcom.mm"
include "biimpi.mm"
include "adantl.mm"
include "eximi.mm"
include "sylbi.mm"
include "adantr.mm"
include "ancri.mm"
include "impbii.mm"
include "bitri.mm"
include "3bitr3i.mm"

theorem gencbvex
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume gencbvex.1: |- A e. _V
  assume gencbvex.2: |- ( A = y -> ( ph <-> ps ) )
  assume gencbvex.3: |- ( A = y -> ( ch <-> th ) )
  assume gencbvex.4: |- ( th <-> E. x ( ch /\ A = y ) )

  disjoint ps x
  disjoint ph y
  disjoint th x
  disjoint ch y
  disjoint A y
  assert |- ( E. x ( ch /\ ph ) <-> E. y ( th /\ ps ) )

  proof
    vy
    cv
    #
    cA
    wceq
    #
    wth
    wps
    wa
    #
    wa
    #
    vy
    wex
    #
    vx
    wex
    @3
    vx
    wex
    #
    vy
    wex
    wch
    wph
    wa
    #
    vx
    wex
    @2
    vy
    wex
    @3
    vx
    vy
    excom
    @4
    @6
    vx
    @2
    @6
    vy
    cA
    gencbvex.1
    @2
    @6
    wb
    cA
    @0
    cA
    @0
    wceq
    #
    @6
    @2
    @7
    wch
    wth
    wph
    wps
    gencbvex.3
    gencbvex.2
    anbi12d
    bicomd
    eqcoms
    ceqsexv
    exbii
    @5
    @2
    vy
    @5
    @1
    vx
    wex
    #
    @2
    wa
    #
    @2
    @1
    @2
    vx
    19.41v
    @9
    @2
    @8
    @2
    simpr
    @2
    @8
    wth
    @8
    wps
    wth
    wch
    @7
    wa
    #
    vx
    wex
    @8
    gencbvex.4
    @10
    @1
    vx
    @7
    @1
    wch
    @7
    @1
    cA
    @0
    eqcom
    biimpi
    adantl
    eximi
    sylbi
    adantr
    ancri
    impbii
    bitri
    exbii
    3bitr3i
end
