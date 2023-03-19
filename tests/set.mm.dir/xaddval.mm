include "cxr.mm"
include "cv.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "cc0.mm"
include "cif.mm"
include "caddc.mm"
include "co.mm"
include "cxad.mm"
include "wa.mm"
include "simpl.mm"
include "eqeq1d.mm"
include "simpr.mm"
include "ifbid.mm"
include "oveq12.mm"
include "ifbieq2d.mm"
include "ifbieq12d.mm"
include "df-xadd.mm"
include "c0ex.mm"
include "pnfex.mm"
include "ifex.mm"
include "mnfxr.mm"
include "elexi.mm"
include "ovex.mm"
include "ovmpt2a.mm"

theorem xaddval
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A +e B ) = if ( A = +oo , if ( B = -oo , 0 , +oo ) , if ( A = -oo , if ( B = +oo , 0 , -oo ) , if ( B = +oo , +oo , if ( B = -oo , -oo , ( A + B ) ) ) ) ) )

  proof
    vx
    vy
    cA
    cB
    cxr
    cxr
    vx
    cv
    #
    cpnf
    wceq
    #
    vy
    cv
    #
    cmnf
    wceq
    #
    cc0
    cpnf
    cif
    #
    @0
    cmnf
    wceq
    #
    @2
    cpnf
    wceq
    #
    cc0
    cmnf
    cif
    #
    @6
    cpnf
    @3
    cmnf
    @0
    @2
    caddc
    co
    #
    cif
    #
    cif
    #
    cif
    #
    cif
    cA
    cpnf
    wceq
    #
    cB
    cmnf
    wceq
    #
    cc0
    cpnf
    cif
    #
    cA
    cmnf
    wceq
    #
    cB
    cpnf
    wceq
    #
    cc0
    cmnf
    cif
    #
    @16
    cpnf
    @13
    cmnf
    cA
    cB
    caddc
    co
    #
    cif
    #
    cif
    #
    cif
    #
    cif
    cxad
    @0
    cA
    wceq
    #
    @2
    cB
    wceq
    #
    wa
    #
    @1
    @12
    @4
    @11
    @14
    @21
    @24
    @0
    cA
    cpnf
    @22
    @23
    simpl
    #
    eqeq1d
    @24
    @3
    @13
    cc0
    cpnf
    @24
    @2
    cB
    cmnf
    @22
    @23
    simpr
    #
    eqeq1d
    #
    ifbid
    @24
    @5
    @15
    @7
    @10
    @17
    @20
    @24
    @0
    cA
    cmnf
    @25
    eqeq1d
    @24
    @6
    @16
    cc0
    cmnf
    @24
    @2
    cB
    cpnf
    @26
    eqeq1d
    #
    ifbid
    @24
    @6
    @16
    @9
    @19
    cpnf
    @28
    @24
    @3
    @13
    @8
    @18
    cmnf
    @27
    @0
    cA
    @2
    cB
    caddc
    oveq12
    ifbieq2d
    ifbieq2d
    ifbieq12d
    ifbieq12d
    vx
    vy
    df-xadd
    @12
    @14
    @21
    @13
    cc0
    cpnf
    c0ex
    pnfex
    ifex
    @15
    @17
    @20
    @16
    cc0
    cmnf
    c0ex
    cmnf
    cxr
    mnfxr
    elexi
    #
    ifex
    @16
    cpnf
    @19
    pnfex
    @13
    cmnf
    @18
    @29
    cA
    cB
    caddc
    ovex
    ifex
    ifex
    ifex
    ifex
    ovmpt2a
end
