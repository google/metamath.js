include "wcel.mm"
include "cint.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "vex.mm"
include "elint.mm"
include "wceq.mm"
include "eleq1.mm"
include "eleq2.mm"
include "imbi12d.mm"
include "spcgv.mm"
include "pm2.43a.mm"
include "syl5bi.mm"
include "ssrdv.mm"

theorem intss1
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let wph: wff ph


  assert |- ( A e. B -> |^| B C_ A )

  proof
    cA
    cB
    wcel
    #
    vx
    cB
    cint
    #
    cA
    vx
    cv
    #
    @1
    wcel
    vy
    cv
    #
    cB
    wcel
    #
    @2
    @3
    wcel
    #
    wi
    #
    vy
    wal
    #
    @0
    @2
    cA
    wcel
    #
    vy
    @2
    cB
    vx
    vex
    elint
    @7
    @0
    @8
    @6
    @0
    @8
    wi
    vy
    cA
    cB
    @3
    cA
    wceq
    @4
    @0
    @5
    @8
    @3
    cA
    cB
    eleq1
    @3
    cA
    @2
    eleq2
    imbi12d
    spcgv
    pm2.43a
    syl5bi
    ssrdv
end
