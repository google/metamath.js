include "cv.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "wal.mm"
include "dfcleq.mm"
include "sylib.mm"
include "19.21bi.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "df-clel.mm"
include "3bitr4g.mm"

theorem eleq2dALT
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  assume eleq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( C e. A <-> C e. B ) )

  proof
    wph
    vx
    cv
    #
    cC
    wceq
    #
    @0
    cA
    wcel
    #
    wa
    #
    vx
    wex
    @1
    @0
    cB
    wcel
    #
    wa
    #
    vx
    wex
    cC
    cA
    wcel
    cC
    cB
    wcel
    wph
    @3
    @5
    vx
    wph
    @2
    @4
    @1
    wph
    @2
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
    eleq1d.1
    vx
    cA
    cB
    dfcleq
    sylib
    19.21bi
    anbi2d
    exbidv
    vx
    cC
    cA
    df-clel
    vx
    cC
    cB
    df-clel
    3bitr4g
end
