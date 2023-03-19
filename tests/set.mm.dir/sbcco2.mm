include "wsbc.mm"
include "cv.mm"
include "wsb.mm"
include "sbsbc.mm"
include "nfv.mm"
include "weq.mm"
include "wceq.mm"
include "wb.mm"
include "equcoms.mm"
include "dfsbcq.mm"
include "bicomd.mm"
include "syl.mm"
include "sbie.mm"
include "bitr3i.mm"

theorem sbcco2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume sbcco2.1: |- ( x = y -> A = B )

  disjoint x y
  disjoint ph y
  disjoint A y
  assert |- ( [. x / y ]. [. B / x ]. ph <-> [. A / x ]. ph )

  proof
    wph
    vx
    cB
    wsbc
    #
    vy
    vx
    cv
    wsbc
    @0
    vy
    vx
    wsb
    wph
    vx
    cA
    wsbc
    #
    @0
    vy
    vx
    sbsbc
    @0
    @1
    vy
    vx
    @1
    vy
    nfv
    vy
    vx
    weq
    cA
    cB
    wceq
    #
    @0
    @1
    wb
    @2
    vx
    vy
    sbcco2.1
    equcoms
    @2
    @1
    @0
    wph
    vx
    cA
    cB
    dfsbcq
    bicomd
    syl
    sbie
    bitr3i
end
