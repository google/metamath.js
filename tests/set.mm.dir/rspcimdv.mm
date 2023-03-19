include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "eleq1d.mm"
include "biimprd.mm"
include "imim12d.mm"
include "spcimdv.mm"
include "mpid.mm"
include "syl5bi.mm"

theorem rspcimdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rspcimdv.1: |- ( ph -> A e. B )
  assume rspcimdv.2: |- ( ( ph /\ x = A ) -> ( ps -> ch ) )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint ch x
  assert |- ( ph -> ( A. x e. B ps -> ch ) )

  proof
    wps
    vx
    cB
    wral
    vx
    cv
    #
    cB
    wcel
    #
    wps
    wi
    #
    vx
    wal
    #
    wph
    wch
    wps
    vx
    cB
    df-ral
    wph
    @3
    cA
    cB
    wcel
    #
    wch
    rspcimdv.1
    wph
    @2
    @4
    wch
    wi
    vx
    cA
    cB
    rspcimdv.1
    wph
    @0
    cA
    wceq
    #
    wa
    #
    @4
    @1
    wps
    wch
    @6
    @1
    @4
    @6
    @0
    cA
    cB
    wph
    @5
    simpr
    eleq1d
    biimprd
    rspcimdv.2
    imim12d
    spcimdv
    mpid
    syl5bi
end
