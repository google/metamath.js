include "ctps.mm"
include "wcel.mm"
include "cv.mm"
include "ctopn.mm"
include "cfv.mm"
include "cbs.mm"
include "ctopon.mm"
include "cab.mm"
include "df-topsp.mm"
include "eleq2i.mm"
include "ctop.mm"
include "cvv.mm"
include "topontop.mm"
include "wn.mm"
include "c0.mm"
include "0ntop.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "con4i.mm"
include "syl.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "elab3.mm"
include "bitri.mm"

theorem istps
  let cA: class A
  let cJ: class J
  let cK: class K
  let vf: setvar f
  assume istps.a: |- A = ( Base ` K )
  assume istps.j: |- J = ( TopOpen ` K )


  assert |- ( K e. TopSp <-> J e. ( TopOn ` A ) )

  proof
    cK
    ctps
    wcel
    cK
    vf
    cv
    #
    ctopn
    cfv
    #
    @0
    cbs
    cfv
    #
    ctopon
    cfv
    #
    wcel
    #
    vf
    cab
    #
    wcel
    cJ
    cA
    ctopon
    cfv
    #
    wcel
    #
    ctps
    @5
    cK
    vf
    df-topsp
    eleq2i
    @4
    @7
    vf
    cK
    @7
    cJ
    ctop
    wcel
    #
    cK
    cvv
    wcel
    #
    cA
    cJ
    topontop
    @9
    @8
    @9
    wn
    #
    @8
    c0
    ctop
    wcel
    0ntop
    @10
    cJ
    c0
    ctop
    @10
    cJ
    cK
    ctopn
    cfv
    #
    c0
    istps.j
    cK
    ctopn
    fvprc
    syl5eq
    eleq1d
    mtbiri
    con4i
    syl
    @0
    cK
    wceq
    #
    @1
    cJ
    @3
    @6
    @12
    @1
    @11
    cJ
    @0
    cK
    ctopn
    fveq2
    istps.j
    syl6eqr
    @12
    @2
    cA
    ctopon
    @12
    @2
    cK
    cbs
    cfv
    cA
    @0
    cK
    cbs
    fveq2
    istps.a
    syl6eqr
    fveq2d
    eleq12d
    elab3
    bitri
end
