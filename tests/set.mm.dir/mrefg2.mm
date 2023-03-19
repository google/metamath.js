include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wb.mm"
include "wa.mm"
include "wss.mm"
include "mrcssid.mm"
include "simpr.mm"
include "mrcssv.mm"
include "adantr.mm"
include "sstrd.mm"
include "impbida.mm"
include "vex.mm"
include "elpw.mm"
include "3bitr4g.mm"
include "anbi1d.mm"
include "elin.mm"
include "pweq.mm"
include "ineq1d.mm"
include "eleq2d.mm"
include "bibi2d.mm"
include "syl5ibrcom.mm"
include "pm5.32rd.mm"
include "rexbidv2.mm"

theorem mrefg2
  let cC: class C
  let cS: class S
  let vg: setvar g
  let cF: class F
  let cX: class X
  let vc: setvar c
  let vs: setvar s
  let vx: setvar x
  assume isnacs.f: |- F = ( mrCls ` C )

  disjoint C g
  disjoint F g
  disjoint S g
  disjoint X g
  disjoint C c
  disjoint C s
  disjoint c g
  disjoint c s
  disjoint g s
  disjoint F c
  disjoint F s
  disjoint S s
  disjoint X c
  disjoint X s
  disjoint X x
  disjoint c x
  disjoint g x
  disjoint s x
  assert |- ( C e. ( Moore ` X ) -> ( E. g e. ( ~P X i^i Fin ) S = ( F ` g ) <-> E. g e. ( ~P S i^i Fin ) S = ( F ` g ) ) )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    cS
    vg
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @3
    vg
    cX
    cpw
    #
    cfn
    cin
    #
    cS
    cpw
    #
    cfn
    cin
    #
    @0
    @3
    @1
    @5
    wcel
    #
    @1
    @7
    wcel
    #
    @0
    @8
    @9
    wb
    @3
    @8
    @1
    @2
    cpw
    #
    cfn
    cin
    #
    wcel
    #
    wb
    @0
    @1
    @4
    wcel
    #
    @1
    cfn
    wcel
    #
    wa
    @1
    @10
    wcel
    #
    @14
    wa
    @8
    @12
    @0
    @13
    @15
    @14
    @0
    @1
    cX
    wss
    #
    @1
    @2
    wss
    #
    @13
    @15
    @0
    @16
    @17
    cC
    @1
    cF
    cX
    isnacs.f
    mrcssid
    @0
    @17
    wa
    @1
    @2
    cX
    @0
    @17
    simpr
    @0
    @2
    cX
    wss
    @17
    cC
    @1
    cF
    cX
    isnacs.f
    mrcssv
    adantr
    sstrd
    impbida
    @1
    cX
    vg
    vex
    #
    elpw
    @1
    @2
    @18
    elpw
    3bitr4g
    anbi1d
    @1
    @4
    cfn
    elin
    @1
    @10
    cfn
    elin
    3bitr4g
    @3
    @9
    @12
    @8
    @3
    @7
    @11
    @1
    @3
    @6
    @10
    cfn
    cS
    @2
    pweq
    ineq1d
    eleq2d
    bibi2d
    syl5ibrcom
    pm5.32rd
    rexbidv2
end
