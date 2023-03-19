include "c9.mm"
include "c10.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cdc.mm"
include "9cn.mm"
include "10nnOLD.mm"
include "nncni.mm"
include "ax-1cn.mm"
include "mulcli.mm"
include "adddii.mm"
include "mulid1i.mm"
include "oveq2i.mm"
include "mulcomi.mm"
include "eqtri.mm"
include "oveq12i.mm"
include "dfdecOLD.mm"
include "3eqtr4i.mm"

theorem 9t11e99OLD



  assert |- ( 9 x. ; 1 1 ) = ; 9 9

  proof
    c9
    c10
    c1
    cmul
    co
    #
    c1
    caddc
    co
    #
    cmul
    co
    #
    c10
    c9
    cmul
    co
    #
    c9
    caddc
    co
    #
    c9
    c1
    c1
    cdc
    #
    cmul
    co
    c9
    c9
    cdc
    @2
    c9
    @0
    cmul
    co
    #
    c9
    c1
    cmul
    co
    #
    caddc
    co
    @4
    c9
    @0
    c1
    9cn
    c10
    c1
    c10
    10nnOLD
    nncni
    #
    ax-1cn
    mulcli
    ax-1cn
    adddii
    @6
    @3
    @7
    c9
    caddc
    @6
    c9
    c10
    cmul
    co
    @3
    @0
    c10
    c9
    cmul
    c10
    @8
    mulid1i
    oveq2i
    c9
    c10
    9cn
    @8
    mulcomi
    eqtri
    c9
    9cn
    mulid1i
    oveq12i
    eqtri
    @5
    @1
    c9
    cmul
    c1
    c1
    dfdecOLD
    oveq2i
    c9
    c9
    dfdecOLD
    3eqtr4i
end
