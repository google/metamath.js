include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "bj-elisset.mm"
include "bj-ceqsalg0.mm"
include "syl.mm"

theorem bj-ceqsalg
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume bj-ceqsalg.1: |- F/ x ps
  assume bj-ceqsalg.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  assert |- ( A e. V -> ( A. x ( x = A -> ph ) <-> ps ) )

  proof
    cA
    cV
    wcel
    vx
    cv
    cA
    wceq
    #
    vx
    wex
    @0
    wph
    wi
    vx
    wal
    wps
    wb
    vx
    cA
    cV
    bj-elisset
    wph
    wps
    @0
    vx
    bj-ceqsalg.1
    bj-ceqsalg.2
    bj-ceqsalg0
    syl
end
