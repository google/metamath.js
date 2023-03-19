include "cfv.mm"
include "wsbc.mm"
include "cv.mm"
include "wbr.mm"
include "weu.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "sbciegf.mm"
include "ax-mp.mm"
include "fvsb.mm"
include "syl5bbr.mm"

theorem fveqsb
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  assume fveqsb.2: |- ( x = ( F ` A ) -> ( ph <-> ps ) )
  assume fveqsb.3: |- F/ x ps

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint F x
  disjoint F y
  assert |- ( E! y A F y -> ( ps <-> E. x ( A. y ( A F y <-> y = x ) /\ ph ) ) )

  proof
    wps
    wph
    vx
    cA
    cF
    cfv
    #
    wsbc
    #
    cA
    vy
    cv
    cF
    wbr
    #
    vy
    weu
    @2
    vy
    vx
    weq
    wb
    vy
    wal
    wph
    wa
    vx
    wex
    @0
    cvv
    wcel
    @1
    wps
    wb
    cA
    cF
    fvex
    wph
    wps
    vx
    @0
    cvv
    fveqsb.3
    fveqsb.2
    sbciegf
    ax-mp
    wph
    vx
    vy
    cA
    cF
    fvsb
    syl5bbr
end
