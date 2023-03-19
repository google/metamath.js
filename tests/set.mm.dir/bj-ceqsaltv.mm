include "wnf.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "w3a.mm"
include "wex.mm"
include "bj-elissetv.mm"
include "3anim3i.mm"
include "bj-ceqsalt0.mm"
include "syl.mm"

theorem bj-ceqsaltv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V

  disjoint A x
  disjoint V x
  assert |- ( ( F/ x ps /\ A. x ( x = A -> ( ph <-> ps ) ) /\ A e. V ) -> ( A. x ( x = A -> ph ) <-> ps ) )

  proof
    wps
    vx
    wnf
    #
    vx
    cv
    cA
    wceq
    #
    wph
    wps
    wb
    wi
    vx
    wal
    #
    cA
    cV
    wcel
    #
    w3a
    @0
    @2
    @1
    vx
    wex
    #
    w3a
    @1
    wph
    wi
    vx
    wal
    wps
    wb
    @3
    @4
    @0
    @2
    vx
    cA
    cV
    bj-elissetv
    3anim3i
    wph
    wps
    @1
    vx
    bj-ceqsalt0
    syl
end
