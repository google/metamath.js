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
include "wb.mm"
include "pm5.5.mm"
include "syl.mm"
include "bicomd.mm"
include "anbi1d.mm"
include "elinintab.mm"
include "cvv.mm"
include "vex.mm"
include "elinintrab.mm"
include "ax-mp.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem inintabd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let vu: setvar u
  assume inintabd.x: |- ( ph -> E. x ps )

  disjoint ps w
  disjoint w x
  disjoint A w
  disjoint A x
  disjoint ph u
  disjoint u w
  disjoint ps u
  disjoint u x
  disjoint A u
  assert |- ( ph -> ( A i^i |^| { x | ps } ) = |^| { w e. ~P A | E. x ( w = ( A i^i x ) /\ ps ) } )

  proof
    wph
    vu
    cA
    wps
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
    wps
    wa
    vx
    wex
    vw
    cA
    cpw
    crab
    cint
    #
    wph
    vu
    cv
    #
    cA
    wcel
    #
    wps
    vu
    vx
    wel
    wi
    vx
    wal
    #
    wa
    wps
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
    wph
    @3
    @6
    @4
    wph
    @6
    @3
    wph
    @5
    @6
    @3
    wb
    inintabd.x
    @5
    @3
    pm5.5
    syl
    bicomd
    anbi1d
    wps
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
    wps
    vx
    vw
    @2
    cA
    cvv
    elinintrab
    ax-mp
    3bitr4g
    eqrdv
end
