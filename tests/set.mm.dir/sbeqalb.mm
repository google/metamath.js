include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "wa.mm"
include "wi.mm"
include "wcel.mm"
include "bibi1.mm"
include "biimpa.mm"
include "biimpd.mm"
include "alanimi.mm"
include "sbceqal.mm"
include "syl5.mm"

theorem sbeqalb
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint A x
  disjoint B x
  assert |- ( A e. V -> ( ( A. x ( ph <-> x = A ) /\ A. x ( ph <-> x = B ) ) -> A = B ) )

  proof
    wph
    vx
    cv
    #
    cA
    wceq
    #
    wb
    #
    vx
    wal
    wph
    @0
    cB
    wceq
    #
    wb
    #
    vx
    wal
    wa
    @1
    @3
    wi
    #
    vx
    wal
    cA
    cV
    wcel
    cA
    cB
    wceq
    @2
    @4
    @5
    vx
    @2
    @4
    wa
    @1
    @3
    @2
    @4
    @1
    @3
    wb
    wph
    @1
    @3
    bibi1
    biimpa
    biimpd
    alanimi
    vx
    cA
    cB
    cV
    sbceqal
    syl5
end
