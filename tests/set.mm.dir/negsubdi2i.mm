include "cmin.mm"
include "co.mm"
include "cneg.mm"
include "caddc.mm"
include "negsubdii.mm"
include "negcli.mm"
include "negsubi.mm"
include "addcomli.mm"
include "eqtri.mm"

theorem negsubdi2i
  let cA: class A
  let cB: class B
  assume negidi.1: |- A e. CC
  assume pncan3i.2: |- B e. CC


  assert |- -u ( A - B ) = ( B - A )

  proof
    cA
    cB
    cmin
    co
    cneg
    cA
    cneg
    #
    cB
    caddc
    co
    cB
    cA
    cmin
    co
    #
    cA
    cB
    negidi.1
    pncan3i.2
    negsubdii
    cB
    @0
    @1
    pncan3i.2
    cA
    negidi.1
    negcli
    cB
    cA
    pncan3i.2
    negidi.1
    negsubi
    addcomli
    eqtri
end
