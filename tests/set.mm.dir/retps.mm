include "cr.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "uniretop.mm"
include "retop.mm"
include "eltpsi.mm"

theorem retps
  let cK: class K
  assume retps.k: |- K = { <. ( Base ` ndx ) , RR >. , <. ( TopSet ` ndx ) , ( topGen ` ran (,) ) >. }


  assert |- K e. TopSp

  proof
    cr
    cioo
    crn
    ctg
    cfv
    cK
    retps.k
    uniretop
    retop
    eltpsi
end
