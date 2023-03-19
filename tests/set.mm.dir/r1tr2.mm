include "cr1.mm"
include "cfv.mm"
include "wtr.mm"
include "cuni.mm"
include "wss.mm"
include "r1tr.mm"
include "df-tr.mm"
include "mpbi.mm"

theorem r1tr2
  let cA: class A


  assert |- U. ( R1 ` A ) C_ ( R1 ` A )

  proof
    cA
    cr1
    cfv
    #
    wtr
    @0
    cuni
    @0
    wss
    cA
    r1tr
    @0
    df-tr
    mpbi
end
