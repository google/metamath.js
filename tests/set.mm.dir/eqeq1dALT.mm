include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wceq.mm"
include "dfcleq.mm"
include "sylib.mm"
include "19.21bi.mm"
include "bibi1d.mm"
include "albidv.mm"
include "3bitr4g.mm"

theorem eqeq1dALT
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
    @0
    cB
    wcel
    #
    @2
    wb
    #
    vx
    wal
    cA
    cC
    wceq
    cB
    cC
    wceq
    wph
    @3
    @5
    vx
    wph
    @1
    @4
    @2
    wph
    @1
    @4
    wb
    #
    vx
    wph
    cA
    cB
    wceq
    @6
    vx
    wal
    eqeq1d.1
    vx
    cA
    cB
    dfcleq
    sylib
    19.21bi
    bibi1d
    albidv
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
