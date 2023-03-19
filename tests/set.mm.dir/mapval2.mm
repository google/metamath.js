include "cmap.mm"
include "co.mm"
include "cxp.mm"
include "cpw.mm"
include "cv.mm"
include "wfn.mm"
include "cab.mm"
include "cin.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "wcel.mm"
include "dff2.mm"
include "ancom.mm"
include "bitri.mm"
include "elmap.mm"
include "elin.mm"
include "selpw.mm"
include "vex.mm"
include "fneq1.mm"
include "elab.mm"
include "anbi12i.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem mapval2
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  assume elmap.1: |- A e. _V
  assume elmap.2: |- B e. _V

  disjoint B f
  disjoint A g
  disjoint f g
  disjoint B g
  disjoint F g
  assert |- ( A ^m B ) = ( ~P ( B X. A ) i^i { f | f Fn B } )

  proof
    vg
    cA
    cB
    cmap
    co
    #
    cB
    cA
    cxp
    #
    cpw
    #
    vf
    cv
    #
    cB
    wfn
    #
    vf
    cab
    #
    cin
    #
    cB
    cA
    vg
    cv
    #
    wf
    #
    @7
    @1
    wss
    #
    @7
    cB
    wfn
    #
    wa
    #
    @7
    @0
    wcel
    @7
    @6
    wcel
    #
    @8
    @10
    @9
    wa
    @11
    cB
    cA
    @7
    dff2
    @10
    @9
    ancom
    bitri
    cA
    cB
    @7
    elmap.1
    elmap.2
    elmap
    @12
    @7
    @2
    wcel
    #
    @7
    @5
    wcel
    #
    wa
    @11
    @7
    @2
    @5
    elin
    @13
    @9
    @14
    @10
    vg
    @1
    selpw
    @4
    @10
    vf
    @7
    vg
    vex
    cB
    @3
    @7
    fneq1
    elab
    anbi12i
    bitri
    3bitr4i
    eqriv
end
