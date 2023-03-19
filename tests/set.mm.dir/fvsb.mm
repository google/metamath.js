include "cfv.mm"
include "wsbc.mm"
include "cv.mm"
include "wbr.mm"
include "cio.mm"
include "weu.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "df-fv.mm"
include "dfsbcq.mm"
include "ax-mp.mm"
include "iotasbc.mm"
include "syl5bb.mm"

theorem fvsb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint F x
  disjoint F y
  assert |- ( E! y A F y -> ( [. ( F ` A ) / x ]. ph <-> E. x ( A. y ( A F y <-> y = x ) /\ ph ) ) )

  proof
    wph
    vx
    cA
    cF
    cfv
    #
    wsbc
    #
    wph
    vx
    cA
    vy
    cv
    #
    cF
    wbr
    #
    vy
    cio
    #
    wsbc
    #
    @3
    vy
    weu
    @3
    @2
    vx
    cv
    wceq
    wb
    vy
    wal
    wph
    wa
    vx
    wex
    @0
    @4
    wceq
    @1
    @5
    wb
    vy
    cA
    cF
    df-fv
    wph
    vx
    @0
    @4
    dfsbcq
    ax-mp
    @3
    wph
    vy
    vx
    iotasbc
    syl5bb
end
