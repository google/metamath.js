include "cz.mm"
include "wss.mm"
include "cc0.mm"
include "wcel.mm"
include "wa.mm"
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
include "cpw.mm"
include "clcmf.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-lcmf.mm"
include "a1i.mm"
include "eleq2.mm"
include "raleq.mm"
include "rabbidv.mm"
include "infeq1d.mm"
include "ifbieq2d.mm"
include "iftrue.mm"
include "adantl.mm"
include "sylan9eqr.mm"
include "cvv.mm"
include "wb.mm"
include "zex.mm"
include "ssex.mm"
include "elpwg.mm"
include "syl.mm"
include "ibir.mm"
include "adantr.mm"
include "simpr.mm"
include "fvmptd.mm"

theorem lcmf0val
  let cZ: class Z
  let vm: setvar m
  let vn: setvar n
  let vz: setvar z


  assert |- ( ( Z C_ ZZ /\ 0 e. Z ) -> ( _lcm ` Z ) = 0 )

  proof
    cZ
    cz
    wss
    #
    cc0
    cZ
    wcel
    #
    wa
    #
    vz
    cZ
    cc0
    vz
    cv
    #
    wcel
    #
    cc0
    vm
    cv
    vn
    cv
    cdvds
    wbr
    #
    vm
    @3
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
    cc0
    cz
    cpw
    #
    clcmf
    cZ
    clcmf
    vz
    @10
    @9
    cmpt
    wceq
    @2
    vz
    vm
    vn
    df-lcmf
    a1i
    @3
    cZ
    wceq
    #
    @2
    @9
    @1
    cc0
    @5
    vm
    cZ
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
    cc0
    @11
    @4
    @1
    @8
    @14
    cc0
    @3
    cZ
    cc0
    eleq2
    @11
    cr
    @7
    @13
    clt
    @11
    @6
    @12
    vn
    cn
    @5
    vm
    @3
    cZ
    raleq
    rabbidv
    infeq1d
    ifbieq2d
    @1
    @15
    cc0
    wceq
    @0
    @1
    cc0
    @14
    iftrue
    adantl
    sylan9eqr
    @0
    cZ
    @10
    wcel
    #
    @1
    @0
    @16
    @0
    cZ
    cvv
    wcel
    @16
    @0
    wb
    cZ
    cz
    zex
    ssex
    cZ
    cz
    cvv
    elpwg
    syl
    ibir
    adantr
    @0
    @1
    simpr
    fvmptd
end
