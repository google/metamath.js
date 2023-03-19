include "wnf.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "ax-gen.mm"
include "ceqsalt.mm"
include "mp3an12.mm"

theorem ceqsalg
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume ceqsalg.1: |- F/ x ps
  assume ceqsalg.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  assert |- ( A e. V -> ( A. x ( x = A -> ph ) <-> ps ) )

  proof
    wps
    vx
    wnf
    vx
    cv
    cA
    wceq
    #
    wph
    wps
    wb
    wi
    #
    vx
    wal
    cA
    cV
    wcel
    @0
    wph
    wi
    vx
    wal
    wps
    wb
    ceqsalg.1
    @1
    vx
    ceqsalg.2
    ax-gen
    wph
    wps
    vx
    cA
    cV
    ceqsalt
    mp3an12
end
