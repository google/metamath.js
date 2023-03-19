include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "caddc.mm"
include "cc0.mm"
include "cmin.mm"
include "wo.mm"
include "cneg.mm"
include "cmul.mm"
include "subsqi.mm"
include "eqeq1i.mm"
include "sqcli.mm"
include "subeq0i.mm"
include "addcli.mm"
include "subcli.mm"
include "mul0ori.mm"
include "3bitr3i.mm"
include "orcom.mm"
include "subnegi.mm"
include "negcli.mm"
include "bitr3i.mm"
include "orbi12i.mm"
include "3bitri.mm"

theorem sqeqori
  let cA: class A
  let cB: class B
  assume binom2.1: |- A e. CC
  assume binom2.2: |- B e. CC


  assert |- ( ( A ^ 2 ) = ( B ^ 2 ) <-> ( A = B \/ A = -u B ) )

  proof
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    wceq
    #
    cA
    cB
    caddc
    co
    #
    cc0
    wceq
    #
    cA
    cB
    cmin
    co
    #
    cc0
    wceq
    #
    wo
    #
    @6
    @4
    wo
    cA
    cB
    wceq
    #
    cA
    cB
    cneg
    #
    wceq
    #
    wo
    @0
    @1
    cmin
    co
    #
    cc0
    wceq
    @3
    @5
    cmul
    co
    #
    cc0
    wceq
    @2
    @7
    @11
    @12
    cc0
    cA
    cB
    binom2.1
    binom2.2
    subsqi
    eqeq1i
    @0
    @1
    cA
    binom2.1
    sqcli
    cB
    binom2.2
    sqcli
    subeq0i
    @3
    @5
    cA
    cB
    binom2.1
    binom2.2
    addcli
    cA
    cB
    binom2.1
    binom2.2
    subcli
    mul0ori
    3bitr3i
    @4
    @6
    orcom
    @6
    @8
    @4
    @10
    cA
    cB
    binom2.1
    binom2.2
    subeq0i
    @4
    cA
    @9
    cmin
    co
    #
    cc0
    wceq
    @10
    @13
    @3
    cc0
    cA
    cB
    binom2.1
    binom2.2
    subnegi
    eqeq1i
    cA
    @9
    binom2.1
    cB
    binom2.2
    negcli
    subeq0i
    bitr3i
    orbi12i
    3bitri
end
