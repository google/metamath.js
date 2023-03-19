include "cv.mm"
include "wcel.mm"
include "cab.mm"
include "cdif.mm"
include "wn.mm"
include "wa.mm"
include "crab.mm"
include "difab.mm"
include "cin.mm"
include "difin.mm"
include "dfrab3.mm"
include "difeq2i.mm"
include "abid2.mm"
include "difeq1i.mm"
include "3eqtr4i.mm"
include "df-rab.mm"

theorem notrab
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A \ { x e. A | ph } ) = { x e. A | -. ph }

  proof
    vx
    cv
    cA
    wcel
    #
    vx
    cab
    #
    wph
    vx
    cab
    #
    cdif
    #
    @0
    wph
    wn
    #
    wa
    vx
    cab
    cA
    wph
    vx
    cA
    crab
    #
    cdif
    #
    @4
    vx
    cA
    crab
    @0
    wph
    vx
    difab
    cA
    cA
    @2
    cin
    #
    cdif
    cA
    @2
    cdif
    @6
    @3
    cA
    @2
    difin
    @5
    @7
    cA
    wph
    vx
    cA
    dfrab3
    difeq2i
    @1
    cA
    @2
    vx
    cA
    abid2
    difeq1i
    3eqtr4i
    @4
    vx
    cA
    df-rab
    3eqtr4i
end
