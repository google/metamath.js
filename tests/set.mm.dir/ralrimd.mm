include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "alrimd.mm"
include "df-ral.mm"
include "syl6ibr.mm"

theorem ralrimd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume ralrimd.1: |- F/ x ph
  assume ralrimd.2: |- F/ x ps
  assume ralrimd.3: |- ( ph -> ( ps -> ( x e. A -> ch ) ) )


  assert |- ( ph -> ( ps -> A. x e. A ch ) )

  proof
    wph
    wps
    vx
    cv
    cA
    wcel
    wch
    wi
    #
    vx
    wal
    wch
    vx
    cA
    wral
    wph
    wps
    @0
    vx
    ralrimd.1
    ralrimd.2
    ralrimd.3
    alrimd
    wch
    vx
    cA
    df-ral
    syl6ibr
end
