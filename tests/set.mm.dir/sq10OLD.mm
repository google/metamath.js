include "c10.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "10nnOLD.mm"
include "nncni.mm"
include "sqvali.mm"
include "caddc.mm"
include "dfdecOLD.mm"
include "dec10OLD.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "oveq1i.mm"
include "mulcli.mm"
include "addid1i.mm"
include "3eqtrri.mm"
include "eqtri.mm"

theorem sq10OLD



  assert |- ( 10 ^ 2 ) = ; ; 1 0 0

  proof
    c10
    c2
    cexp
    co
    c10
    c10
    cmul
    co
    #
    c1
    cc0
    cdc
    #
    cc0
    cdc
    #
    c10
    c10
    10nnOLD
    nncni
    #
    sqvali
    @2
    c10
    @1
    cmul
    co
    #
    cc0
    caddc
    co
    @0
    cc0
    caddc
    co
    @0
    @1
    cc0
    dfdecOLD
    @4
    @0
    cc0
    caddc
    @1
    c10
    c10
    cmul
    c10
    @1
    dec10OLD
    eqcomi
    oveq2i
    oveq1i
    @0
    c10
    c10
    @3
    @3
    mulcli
    addid1i
    3eqtrri
    eqtri
end
