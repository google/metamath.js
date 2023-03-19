include "cmin.mm"
include "cdiv.mm"
include "clog.mm"
include "cfv.mm"
include "efsub.mm"
include "resubcl.mm"
include "relogoprlem.mm"

theorem relogdiv
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR+ /\ B e. RR+ ) -> ( log ` ( A / B ) ) = ( ( log ` A ) - ( log ` B ) ) )

  proof
    cA
    cB
    cmin
    cdiv
    cA
    clog
    cfv
    #
    cB
    clog
    cfv
    #
    efsub
    @0
    @1
    resubcl
    relogoprlem
end
