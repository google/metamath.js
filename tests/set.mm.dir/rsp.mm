include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "sp.mm"
include "sylbi.mm"

theorem rsp
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( A. x e. A ph -> ( x e. A -> ph ) )

  proof
    wph
    vx
    cA
    wral
    vx
    cv
    cA
    wcel
    wph
    wi
    #
    vx
    wal
    @0
    wph
    vx
    cA
    df-ral
    @0
    vx
    sp
    sylbi
end
