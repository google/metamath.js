include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wex.mm"
include "wrex.mm"
include "nfel.mm"
include "nfan.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "spcegf.mm"
include "anabsi5.mm"
include "df-rex.mm"
include "sylibr.mm"

theorem rspcegf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rspcegf.1: |- F/ x ps
  assume rspcegf.2: |- F/_ x A
  assume rspcegf.3: |- F/_ x B
  assume rspcegf.4: |- ( x = A -> ( ph <-> ps ) )


  assert |- ( ( A e. B /\ ps ) -> E. x e. B ph )

  proof
    cA
    cB
    wcel
    #
    wps
    wa
    #
    vx
    cv
    #
    cB
    wcel
    #
    wph
    wa
    #
    vx
    wex
    #
    wph
    vx
    cB
    wrex
    @0
    wps
    @5
    @4
    @1
    vx
    cA
    cB
    rspcegf.2
    @0
    wps
    vx
    vx
    cA
    cB
    rspcegf.2
    rspcegf.3
    nfel
    rspcegf.1
    nfan
    @2
    cA
    wceq
    @3
    @0
    wph
    wps
    @2
    cA
    cB
    eleq1
    rspcegf.4
    anbi12d
    spcegf
    anabsi5
    wph
    vx
    cB
    df-rex
    sylibr
end
