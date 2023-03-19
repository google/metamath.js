include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cha.mm"
include "wcel.mm"
include "cr.mm"
include "csn.mm"
include "ccld.mm"
include "rehaus.mm"
include "uniretop.mm"
include "sncld.mm"
include "mpan.mm"

theorem sncldre
  let cA: class A


  assert |- ( A e. RR -> { A } e. ( Clsd ` ( topGen ` ran (,) ) ) )

  proof
    cioo
    crn
    ctg
    cfv
    #
    cha
    wcel
    cA
    cr
    wcel
    cA
    csn
    @0
    ccld
    cfv
    wcel
    rehaus
    cA
    @0
    cr
    uniretop
    sncld
    mpan
end
