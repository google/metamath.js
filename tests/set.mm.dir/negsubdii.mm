include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "negcli.mm"
include "negdii.mm"
include "negsubi.mm"
include "negeqi.mm"
include "negnegi.mm"
include "oveq2i.mm"
include "3eqtr3i.mm"

theorem negsubdii
  let cA: class A
  let cB: class B
  assume negidi.1: |- A e. CC
  assume pncan3i.2: |- B e. CC


  assert |- -u ( A - B ) = ( -u A + B )

  proof
    cA
    cB
    cneg
    #
    caddc
    co
    #
    cneg
    cA
    cneg
    #
    @0
    cneg
    #
    caddc
    co
    cA
    cB
    cmin
    co
    #
    cneg
    @2
    cB
    caddc
    co
    cA
    @0
    negidi.1
    cB
    pncan3i.2
    negcli
    negdii
    @1
    @4
    cA
    cB
    negidi.1
    pncan3i.2
    negsubi
    negeqi
    @3
    cB
    @2
    caddc
    cB
    pncan3i.2
    negnegi
    oveq2i
    3eqtr3i
end
