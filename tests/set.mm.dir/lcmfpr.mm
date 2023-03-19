include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cpr.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "cn.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "wceq.mm"
include "wo.mm"
include "clcmf.mm"
include "cfv.mm"
include "clcm.mm"
include "co.mm"
include "wb.mm"
include "c0ex.mm"
include "elpr.mm"
include "eqcom.mm"
include "orbi12i.mm"
include "bitri.mm"
include "a1i.mm"
include "breq1.mm"
include "ralprg.mm"
include "rabbidv.mm"
include "infeq1d.mm"
include "ifbieq2d.mm"
include "wss.mm"
include "cfn.mm"
include "prssi.mm"
include "prfi.mm"
include "lcmfval.mm"
include "sylancl.mm"
include "lcmval.mm"
include "3eqtr4d.mm"

theorem lcmfpr
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vn: setvar n


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( _lcm ` { M , N } ) = ( M lcm N ) )

  proof
    cM
    cz
    wcel
    cN
    cz
    wcel
    wa
    #
    cc0
    cM
    cN
    cpr
    #
    wcel
    #
    cc0
    vm
    cv
    #
    vn
    cv
    #
    cdvds
    wbr
    #
    vm
    @1
    wral
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cif
    #
    cM
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wo
    #
    cc0
    cM
    @4
    cdvds
    wbr
    #
    cN
    @4
    cdvds
    wbr
    #
    wa
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cif
    @1
    clcmf
    cfv
    #
    cM
    cN
    clcm
    co
    @0
    @2
    @12
    @8
    @17
    cc0
    @2
    @12
    wb
    @0
    @2
    cc0
    cM
    wceq
    #
    cc0
    cN
    wceq
    #
    wo
    @12
    cc0
    cM
    cN
    c0ex
    elpr
    @19
    @10
    @20
    @11
    cc0
    cM
    eqcom
    cc0
    cN
    eqcom
    orbi12i
    bitri
    a1i
    @0
    cr
    @7
    @16
    clt
    @0
    @6
    @15
    vn
    cn
    @5
    @13
    @14
    vm
    cM
    cN
    cz
    cz
    @3
    cM
    @4
    cdvds
    breq1
    @3
    cN
    @4
    cdvds
    breq1
    ralprg
    rabbidv
    infeq1d
    ifbieq2d
    @0
    @1
    cz
    wss
    @1
    cfn
    wcel
    @18
    @9
    wceq
    cM
    cN
    cz
    prssi
    cM
    cN
    prfi
    vm
    vn
    @1
    lcmfval
    sylancl
    vn
    cM
    cN
    lcmval
    3eqtr4d
end
