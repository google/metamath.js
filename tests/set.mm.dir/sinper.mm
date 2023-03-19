include "c2.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "csin.mm"
include "cmin.mm"
include "sinval.mm"
include "cpi.mm"
include "caddc.mm"
include "sinperlem.mm"

theorem sinper
  let cA: class A
  let cK: class K


  assert |- ( ( A e. CC /\ K e. ZZ ) -> ( sin ` ( A + ( K x. ( 2 x. _pi ) ) ) ) = ( sin ` A ) )

  proof
    cA
    c2
    ci
    cmul
    co
    csin
    cK
    cmin
    cA
    sinval
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
    sinval
    sinperlem
end
