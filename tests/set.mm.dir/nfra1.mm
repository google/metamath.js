include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "nfa1.mm"
include "nfxfr.mm"

theorem nfra1
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- F/ x A. x e. A ph

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
    vx
    wph
    vx
    cA
    df-ral
    @0
    vx
    nfa1
    nfxfr
end
