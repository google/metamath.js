include "cii.mm"
include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "chmph.mm"
include "wbr.mm"
include "cconn.mm"
include "wcel.mm"
include "xrhmph.mm"
include "iiconn.mm"
include "connhmph.mm"
include "mp2.mm"

theorem xrconn



  assert |- ( ordTop ` <_ ) e. Conn

  proof
    cii
    cle
    cordt
    cfv
    #
    chmph
    wbr
    cii
    cconn
    wcel
    @0
    cconn
    wcel
    xrhmph
    iiconn
    cii
    @0
    connhmph
    mp2
end
