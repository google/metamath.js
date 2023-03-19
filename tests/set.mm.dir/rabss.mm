include "crab.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "df-rab.mm"
include "sseq1i.mm"
include "abss.mm"
include "impexp.mm"
include "albii.mm"
include "df-ral.mm"
include "bitr4i.mm"
include "3bitri.mm"

theorem rabss
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint B x
  assert |- ( { x e. A | ph } C_ B <-> A. x e. A ( ph -> x e. B ) )

  proof
    wph
    vx
    cA
    crab
    #
    cB
    wss
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    cB
    wss
    @3
    @1
    cB
    wcel
    #
    wi
    #
    vx
    wal
    #
    wph
    @5
    wi
    #
    vx
    cA
    wral
    #
    @0
    @4
    cB
    wph
    vx
    cA
    df-rab
    sseq1i
    @3
    vx
    cB
    abss
    @7
    @2
    @8
    wi
    #
    vx
    wal
    @9
    @6
    @10
    vx
    @2
    wph
    @5
    impexp
    albii
    @8
    vx
    cA
    df-ral
    bitr4i
    3bitri
end
