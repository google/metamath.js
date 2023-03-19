include "wcel.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "wf.mm"
include "cab.mm"
include "mapvalg.mm"
include "eleq2d.mm"
include "cvv.mm"
include "wi.mm"
include "wb.mm"
include "fex2.mm"
include "3com13.mm"
include "3expia.mm"
include "feq1.mm"
include "elab3g.mm"
include "syl.mm"
include "bitrd.mm"

theorem elmapg
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let vg: setvar g


  assert |- ( ( A e. V /\ B e. W ) -> ( C e. ( A ^m B ) <-> C : B --> A ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cC
    cA
    cB
    cmap
    co
    #
    wcel
    cC
    cB
    cA
    vg
    cv
    #
    wf
    #
    vg
    cab
    #
    wcel
    #
    cB
    cA
    cC
    wf
    #
    @2
    @3
    @6
    cC
    cA
    cB
    cV
    cW
    vg
    mapvalg
    eleq2d
    @2
    @8
    cC
    cvv
    wcel
    #
    wi
    @7
    @8
    wb
    @0
    @1
    @8
    @9
    @8
    @1
    @0
    @9
    cB
    cA
    cC
    cW
    cV
    fex2
    3com13
    3expia
    @5
    @8
    vg
    cC
    cvv
    cB
    cA
    @4
    cC
    feq1
    elab3g
    syl
    bitrd
end
