include "cv.mm"
include "wceq.mm"
include "cab.mm"
include "wcel.mm"
include "wsb.mm"
include "wsbc.mm"
include "eleq1.mm"
include "df-clab.mm"
include "df-sbc.mm"
include "bicomi.mm"
include "3bitr3g.mm"

theorem dfsbcq2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( y = A -> ( [ y / x ] ph <-> [. A / x ]. ph ) )

  proof
    vy
    cv
    #
    cA
    wceq
    @0
    wph
    vx
    cab
    #
    wcel
    cA
    @1
    wcel
    #
    wph
    vx
    vy
    wsb
    wph
    vx
    cA
    wsbc
    #
    @0
    cA
    @1
    eleq1
    wph
    vy
    vx
    df-clab
    @3
    @2
    wph
    vx
    cA
    df-sbc
    bicomi
    3bitr3g
end
