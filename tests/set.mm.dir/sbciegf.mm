include "wcel.mm"
include "wnf.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "wsbc.mm"
include "ax-gen.mm"
include "sbciegft.mm"
include "mp3an23.mm"

theorem sbciegf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume sbciegf.1: |- F/ x ps
  assume sbciegf.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  assert |- ( A e. V -> ( [. A / x ]. ph <-> ps ) )

  proof
    cA
    cV
    wcel
    wps
    vx
    wnf
    vx
    cv
    cA
    wceq
    wph
    wps
    wb
    wi
    #
    vx
    wal
    wph
    vx
    cA
    wsbc
    wps
    wb
    sbciegf.1
    @0
    vx
    sbciegf.2
    ax-gen
    wph
    wps
    vx
    cA
    cV
    sbciegft
    mp3an23
end
