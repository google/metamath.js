include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "crab.mm"
include "wral.mm"
include "wb.mm"
include "abeq2f.mm"
include "pm4.71.mm"
include "albii.mm"
include "bitr4i.mm"
include "df-rab.mm"
include "eqeq2i.mm"
include "df-ral.mm"
include "3bitr4i.mm"

theorem rabid2f
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume rabid2f.1: |- F/_ x A


  assert |- ( A = { x e. A | ph } <-> A. x e. A ph )

  proof
    cA
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    wceq
    #
    @0
    wph
    wi
    #
    vx
    wal
    #
    cA
    wph
    vx
    cA
    crab
    #
    wceq
    wph
    vx
    cA
    wral
    @3
    @0
    @1
    wb
    #
    vx
    wal
    @5
    @1
    vx
    cA
    rabid2f.1
    abeq2f
    @4
    @7
    vx
    @0
    wph
    pm4.71
    albii
    bitr4i
    @6
    @2
    cA
    wph
    vx
    cA
    df-rab
    eqeq2i
    wph
    vx
    cA
    df-ral
    3bitr4i
end
