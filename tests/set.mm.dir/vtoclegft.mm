include "wcel.mm"
include "wnf.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "w3a.mm"
include "wex.mm"
include "elisset.mm"
include "exim.mm"
include "mpan9.mm"
include "3adant2.mm"
include "wb.mm"
include "19.9t.mm"
include "3ad2ant2.mm"
include "mpbid.mm"

theorem vtoclegft
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  assert |- ( ( A e. B /\ F/ x ph /\ A. x ( x = A -> ph ) ) -> ph )

  proof
    cA
    cB
    wcel
    #
    wph
    vx
    wnf
    #
    vx
    cv
    cA
    wceq
    #
    wph
    wi
    vx
    wal
    #
    w3a
    wph
    vx
    wex
    #
    wph
    @0
    @3
    @4
    @1
    @0
    @2
    vx
    wex
    @3
    @4
    vx
    cA
    cB
    elisset
    @2
    wph
    vx
    exim
    mpan9
    3adant2
    @1
    @0
    @4
    wph
    wb
    @3
    wph
    vx
    19.9t
    3ad2ant2
    mpbid
end
