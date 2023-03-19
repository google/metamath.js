include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "alrimih.mm"
include "df-ral.mm"
include "sylibr.mm"

theorem hbralrimi
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param cA: class A
  assume hbralrimi.1: |- ( ph -> A. x ph )
  assume hbralrimi.2: |- ( ph -> ( x e. A -> ps ) )


  assert |- ( ph -> A. x e. A ps )

  proof
    wph
    vx
    cv
    cA
    wcel
    wps
    wi
    #
    vx
    wal
    wps
    vx
    cA
    wral
    wph
    @0
    vx
    hbralrimi.1
    hbralrimi.2
    alrimih
    wps
    vx
    cA
    df-ral
    sylibr
end
