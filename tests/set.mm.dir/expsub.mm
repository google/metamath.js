include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cz.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "cmin.mm"
include "cdiv.mm"
include "wceq.mm"
include "znegcl.mm"
include "expaddz.mm"
include "sylanr2.mm"
include "zcn.mm"
include "negsub.mm"
include "syl2an.mm"
include "adantl.mm"
include "oveq2d.mm"
include "c1.mm"
include "expnegz.mm"
include "3expa.mm"
include "adantrl.mm"
include "expclz.mm"
include "adantrr.mm"
include "expne0i.mm"
include "divrecd.mm"
include "eqtr4d.mm"
include "3eqtr3d.mm"

theorem expsub
  let cA: class A
  let cM: class M
  let cN: class N


  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( M e. ZZ /\ N e. ZZ ) ) -> ( A ^ ( M - N ) ) = ( ( A ^ M ) / ( A ^ N ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    wa
    #
    cA
    cM
    cN
    cneg
    #
    caddc
    co
    #
    cexp
    co
    #
    cA
    cM
    cexp
    co
    #
    cA
    @7
    cexp
    co
    #
    cmul
    co
    #
    cA
    cM
    cN
    cmin
    co
    #
    cexp
    co
    @10
    cA
    cN
    cexp
    co
    #
    cdiv
    co
    #
    @4
    @2
    @3
    @7
    cz
    wcel
    @9
    @12
    wceq
    cN
    znegcl
    cA
    cM
    @7
    expaddz
    sylanr2
    @6
    @8
    @13
    cA
    cexp
    @5
    @8
    @13
    wceq
    #
    @2
    @3
    cM
    cc
    wcel
    cN
    cc
    wcel
    @16
    @4
    cM
    zcn
    cN
    zcn
    cM
    cN
    negsub
    syl2an
    adantl
    oveq2d
    @6
    @12
    @10
    c1
    @14
    cdiv
    co
    #
    cmul
    co
    @15
    @6
    @11
    @17
    @10
    cmul
    @2
    @4
    @11
    @17
    wceq
    #
    @3
    @0
    @1
    @4
    @18
    cA
    cN
    expnegz
    3expa
    adantrl
    oveq2d
    @6
    @10
    @14
    @2
    @3
    @10
    cc
    wcel
    #
    @4
    @0
    @1
    @3
    @19
    cA
    cM
    expclz
    3expa
    adantrr
    @2
    @4
    @14
    cc
    wcel
    #
    @3
    @0
    @1
    @4
    @20
    cA
    cN
    expclz
    3expa
    adantrl
    @2
    @4
    @14
    cc0
    wne
    #
    @3
    @0
    @1
    @4
    @21
    cA
    cN
    expne0i
    3expa
    adantrl
    divrecd
    eqtr4d
    3eqtr3d
end
