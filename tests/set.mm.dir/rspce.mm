include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wex.mm"
include "wrex.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfan.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "spcegf.mm"
include "anabsi5.mm"
include "df-rex.mm"
include "sylibr.mm"

theorem rspce
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rspc.1: |- F/ x ps
  assume rspc.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint B x
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
    vx
    cA
    nfcv
    @0
    wps
    vx
    @0
    vx
    nfv
    rspc.1
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
    rspc.2
    anbi12d
    spcegf
    anabsi5
    wph
    vx
    cB
    df-rex
    sylibr
end
