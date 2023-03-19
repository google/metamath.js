include "cv.mm"
include "wceq.mm"
include "wsbc.mm"
include "cab.mm"
include "wcel.mm"
include "csn.mm"
include "elexi.mm"
include "snid.mm"
include "df-sn.mm"
include "eleqtri.mm"
include "df-sbc.mm"
include "mpbir.mm"

theorem frege54cor1c
  let vx: setvar x
  let cA: class A
  let cC: class C
  assume frege54c.1: |- A e. C

  disjoint A x
  assert |- [. A / x ]. x = A

  proof
    vx
    cv
    cA
    wceq
    #
    vx
    cA
    wsbc
    cA
    @0
    vx
    cab
    #
    wcel
    cA
    cA
    csn
    @1
    cA
    cA
    cC
    frege54c.1
    elexi
    snid
    vx
    cA
    df-sn
    eleqtri
    @0
    vx
    cA
    df-sbc
    mpbir
end
