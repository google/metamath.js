include "c2.mm"
include "ccos.mm"
include "caddc.mm"
include "cosval.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "sinperlem.mm"

theorem cosper
  let cA: class A
  let cK: class K


  assert |- ( ( A e. CC /\ K e. ZZ ) -> ( cos ` ( A + ( K x. ( 2 x. _pi ) ) ) ) = ( cos ` A ) )

  proof
    cA
    c2
    ccos
    cK
    caddc
    cA
    cosval
    cA
    cK
    c2
    cpi
    cmul
    co
    cmul
    co
    caddc
    co
    cosval
    sinperlem
end
