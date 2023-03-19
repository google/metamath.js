include "wcel.mm"
include "crab.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "weu.mm"
include "wreu.mm"
include "cab.mm"
include "df-rab.mm"
include "eqeq1i.mm"
include "absneu.mm"
include "sylan2b.mm"
include "df-reu.mm"
include "sylibr.mm"

theorem rabsneu
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y


  assert |- ( ( A e. V /\ { x e. B | ph } = { A } ) -> E! x e. B ph )

  proof
    cA
    cV
    wcel
    #
    wph
    vx
    cB
    crab
    #
    cA
    csn
    #
    wceq
    #
    wa
    vx
    cv
    cB
    wcel
    wph
    wa
    #
    vx
    weu
    #
    wph
    vx
    cB
    wreu
    @3
    @0
    @4
    vx
    cab
    #
    @2
    wceq
    @5
    @1
    @6
    @2
    wph
    vx
    cB
    df-rab
    eqeq1i
    @4
    vx
    cA
    cV
    absneu
    sylan2b
    wph
    vx
    cB
    df-reu
    sylibr
end
