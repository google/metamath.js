include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "imim3i.mm"
include "al2imi.mm"
include "3imtr4g.mm"
include "sylbi.mm"

theorem ral2imi
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  param cA: class A
  assume ral2imi.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( A. x e. A ph -> ( A. x e. A ps -> A. x e. A ch ) )

  proof
    wph
    vx
    cA
    wral
    vx
    cv
    cA
    wcel
    #
    wph
    wi
    #
    vx
    wal
    #
    wps
    vx
    cA
    wral
    #
    wch
    vx
    cA
    wral
    #
    wi
    wph
    vx
    cA
    df-ral
    @2
    @0
    wps
    wi
    #
    vx
    wal
    @0
    wch
    wi
    #
    vx
    wal
    @3
    @4
    @1
    @5
    @6
    vx
    wph
    wps
    wch
    @0
    ral2imi.1
    imim3i
    al2imi
    wps
    vx
    cA
    df-ral
    wch
    vx
    cA
    df-ral
    3imtr4g
    sylbi
end
