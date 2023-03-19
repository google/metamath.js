include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "wi.mm"
include "wa.mm"
include "wcel.mm"
include "wsbc.mm"
include "albiim.mm"
include "sbc6g.mm"
include "bicomd.mm"
include "anbi2d.mm"
include "syl5bb.mm"

theorem pm14.122a
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint ph y
  assert |- ( A e. V -> ( A. x ( ph <-> x = A ) <-> ( A. x ( ph -> x = A ) /\ [. A / x ]. ph ) ) )

  proof
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
    @0
    wph
    wi
    vx
    wal
    #
    wa
    cA
    cV
    wcel
    #
    @1
    wph
    vx
    cA
    wsbc
    #
    wa
    wph
    @0
    vx
    albiim
    @3
    @2
    @4
    @1
    @3
    @4
    @2
    wph
    vx
    cA
    cV
    sbc6g
    bicomd
    anbi2d
    syl5bb
end
