include "cab.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "ssab.mm"
include "df-ral.mm"
include "bitr4i.mm"

theorem ssabral
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A C_ { x | ph } <-> A. x e. A ph )

  proof
    cA
    wph
    vx
    cab
    wss
    vx
    cv
    cA
    wcel
    wph
    wi
    vx
    wal
    wph
    vx
    cA
    wral
    wph
    vx
    cA
    ssab
    wph
    vx
    cA
    df-ral
    bitr4i
end
