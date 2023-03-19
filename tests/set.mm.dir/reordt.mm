include "cmnf.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cr.mm"
include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "ioomax.mm"
include "iooordt.mm"
include "eqeltrri.mm"

theorem reordt



  assert |- RR e. ( ordTop ` <_ )

  proof
    cmnf
    cpnf
    cioo
    co
    cr
    cle
    cordt
    cfv
    ioomax
    cmnf
    cpnf
    iooordt
    eqeltrri
end
