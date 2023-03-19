include "csb.mm"
include "cv.mm"
include "wcel.mm"
include "wsbc.mm"
include "df-csb.mm"
include "abeq2i.mm"
include "nfcri.mm"
include "sbcgfi.mm"
include "bitri.mm"
include "eqriv.mm"

theorem csbgfi
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume csbgfi.1: |- A e. _V
  assume csbgfi.2: |- F/_ x B


  assert |- [_ A / x ]_ B = B

  proof
    vy
    vx
    cA
    cB
    csb
    #
    cB
    vy
    cv
    #
    @0
    wcel
    @1
    cB
    wcel
    #
    vx
    cA
    wsbc
    #
    @2
    @3
    vy
    @0
    vx
    vy
    cA
    cB
    df-csb
    abeq2i
    @2
    vx
    cA
    csbgfi.1
    vx
    vy
    cB
    csbgfi.2
    nfcri
    sbcgfi
    bitri
    eqriv
end
