include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "wi.mm"
include "wsbc.mm"
include "wa.mm"
include "wex.mm"
include "pm14.122a.mm"
include "pm14.122b.mm"
include "bitrd.mm"

theorem pm14.122c
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint ph y
  assert |- ( A e. V -> ( A. x ( ph <-> x = A ) <-> ( A. x ( ph -> x = A ) /\ E. x ph ) ) )

  proof
    cA
    cV
    wcel
    wph
    vx
    cv
    cA
    wceq
    #
    wb
    vx
    wal
    wph
    @0
    wi
    vx
    wal
    #
    wph
    vx
    cA
    wsbc
    wa
    @1
    wph
    vx
    wex
    wa
    wph
    vx
    cA
    cV
    pm14.122a
    wph
    vx
    cA
    cV
    pm14.122b
    bitrd
end
