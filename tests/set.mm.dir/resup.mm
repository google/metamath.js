include "cmnf.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cr.mm"
include "ioomax.mm"
include "supeq1i.mm"
include "wcel.mm"
include "wne.mm"
include "wceq.mm"
include "mnfxr.mm"
include "mnfnepnf.mm"
include "ioopnfsup.mm"
include "mp2an.mm"
include "eqtr3i.mm"

theorem resup



  assert |- sup ( RR , RR* , < ) = +oo

  proof
    cmnf
    cpnf
    cioo
    co
    #
    cxr
    clt
    csup
    #
    cr
    cxr
    clt
    csup
    cpnf
    cxr
    @0
    cr
    clt
    ioomax
    supeq1i
    cmnf
    cxr
    wcel
    cmnf
    cpnf
    wne
    @1
    cpnf
    wceq
    mnfxr
    mnfnepnf
    cmnf
    ioopnfsup
    mp2an
    eqtr3i
end
