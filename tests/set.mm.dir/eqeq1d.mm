include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wceq.mm"
include "dfcleq.mm"
include "biimpi.mm"
include "bibi1.mm"
include "alimi.mm"
include "albi.mm"
include "4syl.mm"
include "3bitr4g.mm"

theorem eqeq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  assume eqeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( A = C <-> B = C ) )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    #
    @0
    cC
    wcel
    #
    wb
    #
    vx
    wal
    #
    @0
    cB
    wcel
    #
    @2
    wb
    #
    vx
    wal
    #
    cA
    cC
    wceq
    cB
    cC
    wceq
    wph
    cA
    cB
    wceq
    #
    @1
    @5
    wb
    #
    vx
    wal
    #
    @3
    @6
    wb
    #
    vx
    wal
    @4
    @7
    wb
    eqeq1d.1
    @8
    @10
    vx
    cA
    cB
    dfcleq
    biimpi
    @9
    @11
    vx
    @1
    @5
    @2
    bibi1
    alimi
    @3
    @6
    vx
    albi
    4syl
    vx
    cA
    cC
    dfcleq
    vx
    cB
    cC
    dfcleq
    3bitr4g
end
