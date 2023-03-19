include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "wceq.mm"
include "wex.mm"
include "clelab.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "simprbda.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "df-rab.mm"
include "eleq2s.mm"

theorem elrabi
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V

  disjoint A x
  disjoint V x
  assert |- ( A e. { x e. V | ph } -> A e. V )

  proof
    cA
    cV
    wcel
    #
    cA
    vx
    cv
    #
    cV
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    wph
    vx
    cV
    crab
    cA
    @4
    wcel
    @1
    cA
    wceq
    #
    @3
    wa
    #
    vx
    wex
    @0
    @3
    vx
    cA
    clelab
    @6
    @0
    vx
    @5
    @3
    @0
    wph
    @5
    @2
    @0
    wph
    @1
    cA
    cV
    eleq1
    anbi1d
    simprbda
    exlimiv
    sylbi
    wph
    vx
    cV
    df-rab
    eleq2s
end
