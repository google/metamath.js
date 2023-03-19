include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "wal.mm"
include "crab.mm"
include "wral.mm"
include "ab0.mm"
include "df-rab.mm"
include "eqeq1i.mm"
include "raln.mm"
include "3bitr4i.mm"

theorem rabeq0
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( { x e. A | ph } = (/) <-> A. x e. A -. ph )

  proof
    vx
    cv
    cA
    wcel
    wph
    wa
    #
    vx
    cab
    #
    c0
    wceq
    @0
    wn
    vx
    wal
    wph
    vx
    cA
    crab
    #
    c0
    wceq
    wph
    wn
    vx
    cA
    wral
    @0
    vx
    ab0
    @2
    @1
    c0
    wph
    vx
    cA
    df-rab
    eqeq1i
    wph
    vx
    cA
    raln
    3bitr4i
end
