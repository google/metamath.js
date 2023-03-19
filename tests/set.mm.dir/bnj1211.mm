include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "sylib.mm"

theorem bnj1211
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume bnj1211.1: |- ( ph -> A. x e. A ps )


  assert |- ( ph -> A. x ( x e. A -> ps ) )

  proof
    wph
    wps
    vx
    cA
    wral
    vx
    cv
    cA
    wcel
    wps
    wi
    vx
    wal
    bnj1211.1
    wps
    vx
    cA
    df-ral
    sylib
end
