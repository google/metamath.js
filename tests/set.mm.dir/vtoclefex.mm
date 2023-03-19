include "wcel.mm"
include "wnf.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "ax-gen.mm"
include "vtoclegft.mm"
include "mp3an23.mm"

theorem vtoclefex
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume vtoclefex.1: |- F/ x ph
  assume vtoclefex.3: |- ( x = A -> ph )

  disjoint A x
  assert |- ( A e. V -> ph )

  proof
    cA
    cV
    wcel
    wph
    vx
    wnf
    vx
    cv
    cA
    wceq
    wph
    wi
    #
    vx
    wal
    wph
    vtoclefex.1
    @0
    vx
    vtoclefex.3
    ax-gen
    wph
    vx
    cA
    cV
    vtoclegft
    mp3an23
end
