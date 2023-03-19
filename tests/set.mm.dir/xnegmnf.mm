include "cmnf.mm"
include "cxne.mm"
include "cpnf.mm"
include "wceq.mm"
include "cneg.mm"
include "cif.mm"
include "df-xneg.mm"
include "wne.mm"
include "mnfnepnf.mm"
include "ifnefalse.mm"
include "ax-mp.mm"
include "eqid.mm"
include "iftruei.mm"
include "3eqtri.mm"

theorem xnegmnf



  assert |- -e -oo = +oo

  proof
    cmnf
    cxne
    cmnf
    cpnf
    wceq
    cmnf
    cmnf
    cmnf
    wceq
    #
    cpnf
    cmnf
    cneg
    #
    cif
    #
    cif
    #
    @2
    cpnf
    cmnf
    df-xneg
    cmnf
    cpnf
    wne
    @3
    @2
    wceq
    mnfnepnf
    cmnf
    cpnf
    cmnf
    @2
    ifnefalse
    ax-mp
    @0
    cpnf
    @1
    cmnf
    eqid
    iftruei
    3eqtri
end
