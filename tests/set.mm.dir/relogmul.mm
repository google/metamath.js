include "caddc.mm"
include "cmul.mm"
include "clog.mm"
include "cfv.mm"
include "efadd.mm"
include "readdcl.mm"
include "relogoprlem.mm"

theorem relogmul
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR+ /\ B e. RR+ ) -> ( log ` ( A x. B ) ) = ( ( log ` A ) + ( log ` B ) ) )

  proof
    cA
    cB
    caddc
    cmul
    cA
    clog
    cfv
    #
    cB
    clog
    cfv
    #
    efadd
    @0
    @1
    readdcl
    relogoprlem
end
