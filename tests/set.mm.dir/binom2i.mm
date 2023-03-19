include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "c2.mm"
include "cexp.mm"
include "addcli.mm"
include "adddii.mm"
include "adddiri.mm"
include "mulcomi.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "oveq12i.mm"
include "mulcli.mm"
include "addassi.mm"
include "oveq1i.mm"
include "3eqtr2i.mm"
include "sqvali.mm"
include "2timesi.mm"
include "3eqtr4i.mm"

theorem binom2i
  let cA: class A
  let cB: class B
  assume binom2.1: |- A e. CC
  assume binom2.2: |- B e. CC


  assert |- ( ( A + B ) ^ 2 ) = ( ( ( A ^ 2 ) + ( 2 x. ( A x. B ) ) ) + ( B ^ 2 ) )

  proof
    cA
    cB
    caddc
    co
    #
    @0
    cmul
    co
    #
    cA
    cA
    cmul
    co
    #
    cA
    cB
    cmul
    co
    #
    @3
    caddc
    co
    #
    caddc
    co
    #
    cB
    cB
    cmul
    co
    #
    caddc
    co
    #
    @0
    c2
    cexp
    co
    cA
    c2
    cexp
    co
    #
    c2
    @3
    cmul
    co
    #
    caddc
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    @1
    @0
    cA
    cmul
    co
    #
    @0
    cB
    cmul
    co
    #
    caddc
    co
    #
    @7
    @0
    cA
    cB
    cA
    cB
    binom2.1
    binom2.2
    addcli
    #
    binom2.1
    binom2.2
    adddii
    @14
    @2
    @3
    caddc
    co
    #
    @3
    @6
    caddc
    co
    #
    caddc
    co
    @16
    @3
    caddc
    co
    #
    @6
    caddc
    co
    @7
    @12
    @16
    @13
    @17
    caddc
    @12
    @2
    cB
    cA
    cmul
    co
    #
    caddc
    co
    @16
    cA
    cB
    cA
    binom2.1
    binom2.2
    binom2.1
    adddiri
    @19
    @3
    @2
    caddc
    cB
    cA
    binom2.2
    binom2.1
    mulcomi
    oveq2i
    eqtri
    cA
    cB
    cB
    binom2.1
    binom2.2
    binom2.2
    adddiri
    oveq12i
    @16
    @3
    @6
    @2
    @3
    cA
    cA
    binom2.1
    binom2.1
    mulcli
    #
    cA
    cB
    binom2.1
    binom2.2
    mulcli
    #
    addcli
    @21
    cB
    cB
    binom2.2
    binom2.2
    mulcli
    addassi
    @18
    @5
    @6
    caddc
    @2
    @3
    @3
    @20
    @21
    @21
    addassi
    oveq1i
    3eqtr2i
    eqtri
    @0
    @15
    sqvali
    @10
    @5
    @11
    @6
    caddc
    @8
    @2
    @9
    @4
    caddc
    cA
    binom2.1
    sqvali
    @3
    @21
    2timesi
    oveq12i
    cB
    binom2.2
    sqvali
    oveq12i
    3eqtr4i
end
