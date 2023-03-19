include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "df-ral.mm"
include "sylibr.mm"

theorem bnj1142
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume bnj1142.1: |- ( ph -> A. x ( x e. A -> ps ) )


  assert |- ( ph -> A. x e. A ps )

  proof
    wph
    vx
    cv
    cA
    wcel
    wps
    wi
    vx
    wal
    wps
    vx
    cA
    wral
    bnj1142.1
    wps
    vx
    cA
    df-ral
    sylibr
end
