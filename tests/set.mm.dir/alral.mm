include "wal.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "ala1.mm"
include "df-ral.mm"
include "sylibr.mm"

theorem alral
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( A. x ph -> A. x e. A ph )

  proof
    wph
    vx
    wal
    vx
    cv
    cA
    wcel
    #
    wph
    wi
    vx
    wal
    wph
    vx
    cA
    wral
    wph
    @0
    vx
    ala1
    wph
    vx
    cA
    df-ral
    sylibr
end
