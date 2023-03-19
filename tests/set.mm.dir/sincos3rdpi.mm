include "cpi.mm"
include "c3.mm"
include "cdiv.mm"
include "co.mm"
include "csin.mm"
include "cfv.mm"
include "csqrt.mm"
include "c2.mm"
include "wceq.mm"
include "ccos.mm"
include "c1.mm"
include "cmin.mm"
include "c6.mm"
include "cmul.mm"
include "picn.mm"
include "2cn.mm"
include "2ne0.mm"
include "reccli.mm"
include "3cn.mm"
include "3ne0.mm"
include "subdii.mm"
include "caddc.mm"
include "halfpm6th.mm"
include "simpli.mm"
include "oveq2i.mm"
include "cc.mm"
include "wcel.mm"
include "6cn.mm"
include "6nn.mm"
include "nnne0i.mm"
include "nncan.mm"
include "mp2an.mm"
include "eqtr3i.mm"
include "divreci.mm"
include "oveq12i.mm"
include "3eqtr4i.mm"
include "fveq2i.mm"
include "divcli.mm"
include "coshalfpim.mm"
include "ax-mp.mm"
include "sincos6thpi.mm"
include "simpri.mm"
include "3eqtr3i.mm"
include "sinhalfpim.mm"
include "pm3.2i.mm"

theorem sincos3rdpi



  assert |- ( ( sin ` ( _pi / 3 ) ) = ( ( sqrt ` 3 ) / 2 ) /\ ( cos ` ( _pi / 3 ) ) = ( 1 / 2 ) )

  proof
    cpi
    c3
    cdiv
    co
    #
    csin
    cfv
    #
    c3
    csqrt
    cfv
    c2
    cdiv
    co
    #
    wceq
    @0
    ccos
    cfv
    #
    c1
    c2
    cdiv
    co
    #
    wceq
    cpi
    c2
    cdiv
    co
    #
    @0
    cmin
    co
    #
    ccos
    cfv
    #
    cpi
    c6
    cdiv
    co
    #
    ccos
    cfv
    #
    @1
    @2
    @6
    @8
    ccos
    cpi
    @4
    cmul
    co
    #
    cpi
    c1
    c3
    cdiv
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cpi
    c1
    c6
    cdiv
    co
    #
    cmul
    co
    #
    @6
    @8
    cpi
    @4
    @11
    cmin
    co
    #
    cmul
    co
    @13
    @15
    cpi
    @4
    @11
    picn
    c2
    2cn
    2ne0
    reccli
    #
    c3
    3cn
    3ne0
    reccli
    subdii
    @16
    @14
    cpi
    cmul
    @4
    @4
    @14
    cmin
    co
    #
    cmin
    co
    #
    @16
    @14
    @18
    @11
    @4
    cmin
    @18
    @11
    wceq
    @4
    @14
    caddc
    co
    c2
    c3
    cdiv
    co
    wceq
    halfpm6th
    simpli
    oveq2i
    @4
    cc
    wcel
    @14
    cc
    wcel
    @19
    @14
    wceq
    @17
    c6
    6cn
    c6
    6nn
    nnne0i
    #
    reccli
    @4
    @14
    nncan
    mp2an
    eqtr3i
    oveq2i
    eqtr3i
    @5
    @10
    @0
    @12
    cmin
    cpi
    c2
    picn
    2cn
    2ne0
    divreci
    cpi
    c3
    picn
    3cn
    3ne0
    divreci
    oveq12i
    cpi
    c6
    picn
    6cn
    @20
    divreci
    3eqtr4i
    #
    fveq2i
    @0
    cc
    wcel
    #
    @7
    @1
    wceq
    cpi
    c3
    picn
    3cn
    3ne0
    divcli
    #
    @0
    coshalfpim
    ax-mp
    @8
    csin
    cfv
    #
    @4
    wceq
    #
    @9
    @2
    wceq
    #
    sincos6thpi
    simpri
    3eqtr3i
    @6
    csin
    cfv
    #
    @24
    @3
    @4
    @6
    @8
    csin
    @21
    fveq2i
    @22
    @27
    @3
    wceq
    @23
    @0
    sinhalfpim
    ax-mp
    @25
    @26
    sincos6thpi
    simpli
    3eqtr3i
    pm3.2i
end
