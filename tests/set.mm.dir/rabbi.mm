include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "wal.mm"
include "cab.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "abbi.mm"
include "wi.mm"
include "df-ral.mm"
include "pm5.32.mm"
include "albii.mm"
include "bitri.mm"
include "df-rab.mm"
include "eqeq12i.mm"
include "3bitr4i.mm"

theorem rabbi
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A


  assert |- ( A. x e. A ( ps <-> ch ) <-> { x e. A | ps } = { x e. A | ch } )

  proof
    vx
    cv
    cA
    wcel
    #
    wps
    wa
    #
    @0
    wch
    wa
    #
    wb
    #
    vx
    wal
    #
    @1
    vx
    cab
    #
    @2
    vx
    cab
    #
    wceq
    wps
    wch
    wb
    #
    vx
    cA
    wral
    #
    wps
    vx
    cA
    crab
    #
    wch
    vx
    cA
    crab
    #
    wceq
    @1
    @2
    vx
    abbi
    @8
    @0
    @7
    wi
    #
    vx
    wal
    @4
    @7
    vx
    cA
    df-ral
    @11
    @3
    vx
    @0
    wps
    wch
    pm5.32
    albii
    bitri
    @9
    @5
    @10
    @6
    wps
    vx
    cA
    df-rab
    wch
    vx
    cA
    df-rab
    eqeq12i
    3bitr4i
end
