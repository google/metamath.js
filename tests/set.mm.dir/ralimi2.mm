include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "alimi.mm"
include "df-ral.mm"
include "3imtr4i.mm"

theorem ralimi2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ralimi2.1: |- ( ( x e. A -> ph ) -> ( x e. B -> ps ) )


  assert |- ( A. x e. A ph -> A. x e. B ps )

  proof
    vx
    cv
    #
    cA
    wcel
    wph
    wi
    #
    vx
    wal
    @0
    cB
    wcel
    wps
    wi
    #
    vx
    wal
    wph
    vx
    cA
    wral
    wps
    vx
    cB
    wral
    @1
    @2
    vx
    ralimi2.1
    alimi
    wph
    vx
    cA
    df-ral
    wps
    vx
    cB
    df-ral
    3imtr4i
end
