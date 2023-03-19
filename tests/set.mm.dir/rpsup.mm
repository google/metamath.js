include "cc0.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "crp.mm"
include "ioorp.mm"
include "supeq1i.mm"
include "wcel.mm"
include "wne.mm"
include "wceq.mm"
include "0xr.mm"
include "cr.mm"
include "0re.mm"
include "renepnf.mm"
include "ax-mp.mm"
include "ioopnfsup.mm"
include "mp2an.mm"
include "eqtr3i.mm"

theorem rpsup



  assert |- sup ( RR+ , RR* , < ) = +oo

  proof
    cc0
    cpnf
    cioo
    co
    #
    cxr
    clt
    csup
    #
    crp
    cxr
    clt
    csup
    cpnf
    cxr
    @0
    crp
    clt
    ioorp
    supeq1i
    cc0
    cxr
    wcel
    cc0
    cpnf
    wne
    #
    @1
    cpnf
    wceq
    0xr
    cc0
    cr
    wcel
    @2
    0re
    cc0
    renepnf
    ax-mp
    cc0
    ioopnfsup
    mp2an
    eqtr3i
end
