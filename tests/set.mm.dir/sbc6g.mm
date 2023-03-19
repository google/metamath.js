include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "wsbc.mm"
include "alexeqg.mm"
include "sbc5.mm"
include "syl6rbbr.mm"

theorem sbc6g
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V

  disjoint A x
  assert |- ( A e. V -> ( [. A / x ]. ph <-> A. x ( x = A -> ph ) ) )

  proof
    cA
    cV
    wcel
    vx
    cv
    cA
    wceq
    #
    wph
    wi
    vx
    wal
    @0
    wph
    wa
    vx
    wex
    wph
    vx
    cA
    wsbc
    wph
    vx
    cA
    cV
    alexeqg
    wph
    vx
    cA
    sbc5
    syl6rbbr
end
