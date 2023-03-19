include "cab.mm"
include "cint.mm"
include "cin.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cpw.mm"
include "crab.mm"
include "wcel.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "ax-1.mm"
include "anim1i.mm"
include "elinintab.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "elinintrab.mm"
include "ax-mp.mm"
include "3imtr4i.mm"
include "ssriv.mm"

theorem inintabss
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let vu: setvar u

  disjoint ph w
  disjoint w x
  disjoint A w
  disjoint A x
  disjoint u w
  disjoint ph u
  disjoint u x
  disjoint A u
  assert |- ( A i^i |^| { x | ph } ) C_ |^| { w e. ~P A | E. x ( w = ( A i^i x ) /\ ph ) }

  proof
    vu
    cA
    wph
    vx
    cab
    cint
    cin
    #
    vw
    cv
    cA
    vx
    cv
    cin
    wceq
    wph
    wa
    vx
    wex
    vw
    cA
    cpw
    crab
    cint
    #
    vu
    cv
    #
    cA
    wcel
    #
    wph
    vu
    vx
    wel
    wi
    vx
    wal
    #
    wa
    wph
    vx
    wex
    #
    @3
    wi
    #
    @4
    wa
    #
    @2
    @0
    wcel
    @2
    @1
    wcel
    #
    @3
    @6
    @4
    @3
    @5
    ax-1
    anim1i
    wph
    vx
    @2
    cA
    elinintab
    @2
    cvv
    wcel
    @8
    @7
    wb
    vu
    vex
    wph
    vx
    vw
    @2
    cA
    cvv
    elinintrab
    ax-mp
    3imtr4i
    ssriv
end
